#include "poly_batch.h"

#include <stdio.h>
#include <stdlib.h>

#include "util.h"

static void fast_linear_comp(fmpz_mod_poly_t poly, const fmpz_mod_ctx_t ctx, const struct tree_s* const pre, const int n_points, fmpz_t* const pointsX, fmpz_t* const pointsY);
static void fast_interpolate(fmpz_mod_poly_t poly, const fmpz_mod_ctx_t ctx, const struct precomp_s* const pre, const fmpz_t* const pointsY);
static void fast_evaluate(fmpz_t* const pointsY, const fmpz_mod_poly_t poly, const fmpz_mod_ctx_t ctx, const struct tree_s* const pre, const int n_points, const fmpz_t* const pointsX);

static void tree_init(struct tree_s* const pre, const fmpz_mod_ctx_t ctx, const int n_points, const fmpz_t* const pointsX);
void tree_clear(struct tree_s* const pre, const fmpz_mod_ctx_t ctx);

static void c_precomp_init(struct precomp_s* const pre, const fmpz_t modulus, const int n_points, const fmpz_t* const pointsX);

void poly_batch_init(fmpz_mod_poly_t poly, const struct precomp_s* const pre) {
  fmpz_mod_poly_init(poly, pre->ctx);
  fmpz_mod_poly_set_coeff_ui(poly, 0, 0, pre->ctx);
}

void poly_batch_clear(fmpz_mod_poly_t poly, const struct precomp_s* const pre) {
  fmpz_mod_poly_clear(poly, pre->ctx);
}

char* poly_batch_evaluate_once(const fmpz_mod_poly_t poly, char* modulus, char* xIn) {
  fmpz_t x; fmpz_init_from_gostr(x, xIn);
  fmpz_t y; fmpz_init(y);
  fmpz_t mod; fmpz_init_from_gostr(mod, modulus);
  fmpz_mod_ctx_t ctx; fmpz_mod_ctx_init(ctx, mod);

  fmpz_mod_poly_evaluate_fmpz(y, poly, x, ctx);
  char* out = fmpz_get_str(NULL, 16, y);

  fmpz_clear(x);
  fmpz_clear(y);
  fmpz_clear(mod);
  fmpz_mod_ctx_clear(ctx);

  return out;
}

char* poly_batch_evaluate(fmpz_mod_poly_t poly, char* modulus, const int n_points, char** pointsXin) {
  fmpz_t mod; fmpz_init_from_gostr(mod, modulus);
  fmpz_mod_ctx_t ctx; fmpz_mod_ctx_init(ctx, mod);
  fmpz_t xs[n_points];
  fmpz_t ys[n_points];
  for (int i = 0; i < n_points; i++) {
    fmpz_init_from_gostr(xs[i], pointsXin[i]);
    fmpz_init(ys[i]);
  }

  fmpz_mod_poly_evaluate_fmpz_vec_fast(ys[0], poly, xs[0], n_points, ctx);

  for (int i = 0; i < n_points; i++) {
    fmpz_clear(xs[i]);
  }
  fmpz_mod_ctx_clear(ctx);
  fmpz_clear(mod);

  return fmpz_array_to_str(n_points, ys);
}


void poly_batch_interpolate(fmpz_mod_poly_t poly, const struct precomp_s* const pre, char** pointsYin) {
  // We use the algorithm from:
  //    "Modern Computer Algebra"
  //    Joachim von zur Gathen and Jurgen Gerhard
  //    Chapter 10, Algorithm 10.11
  fmpz_t pointsY[pre->n_points];

  for (int i = 0; i < pre->n_points; i++) {
    fmpz_init_from_gostr(pointsY[i], pointsYin[i]);
  }

  fast_interpolate(poly, pre->ctx, pre, pointsY);

  for (int i = 0; i < pre->n_points; i++) {
    fmpz_clear(pointsY[i]);
  }
}

static void tree_init(struct tree_s* const pre, const fmpz_mod_ctx_t ctx, const int n_points, const fmpz_t* const pointsX) {
  // On input (x_1, ..., x_n), compute the polynomial
  //    f(x) = (x - x_1)(x - x_2) ... (x - x_n)
  // using a divide-and-conquer approach, saving the
  // intermediate results in a tree.

  fmpz_mod_poly_init(pre->poly, ctx);
  fmpz_mod_poly_zero(pre->poly, ctx);

  if (n_points == 1) {
    pre->left = NULL;
    pre->right = NULL;

    fmpz_t tmp;
    fmpz_init_set(tmp, pointsX[0]);
    fmpz_neg(tmp, tmp);

    // In base case, polynomial is (x - x_i)
    fmpz_mod_poly_set_coeff_ui(pre->poly, 1, 1, ctx);
    fmpz_mod_poly_set_coeff_fmpz(pre->poly, 0, tmp, ctx);
    fmpz_clear(tmp);
    return;
  }

  pre->left = safe_malloc(sizeof(struct tree_s));
  pre->right = safe_malloc(sizeof(struct tree_s));

  if (!pre->left || !pre->right) {
    fprintf(stderr, "Ran out of memory!\n");
    exit(1);
  }

  const int k = n_points / 2;
  // Compute the left polynomial recursively on the first k points
  tree_init(pre->left, ctx, k, pointsX);

  // Compute the right polynomial on the rest of the points
  tree_init(pre->right, ctx, n_points - k, &pointsX[k]);

  // Store the product
  fmpz_mod_poly_mul(pre->poly, pre->left->poly, pre->right->poly, ctx);
}

static void c_precomp_init(struct precomp_s* const pre, const fmpz_t modulus, const int n_points, const fmpz_t* const pointsX) {
  pre->x_points = safe_malloc(n_points * sizeof(fmpz_t));
  pre->s_points = safe_malloc(n_points * sizeof(fmpz_t));
  fmpz_mod_ctx_t ctx; fmpz_mod_ctx_init(ctx, modulus);

  for (int i = 0; i < n_points; i++) {
    fmpz_init_set(pre->x_points[i], pointsX[i]);
    fmpz_init(pre->s_points[i]);
  }

  pre->n_points = n_points;
  tree_init(&pre->tree, ctx, n_points, pointsX);

  // Compute derivative of the roots
  fmpz_mod_poly_init(pre->deriv, ctx);
  fmpz_mod_poly_derivative(pre->deriv, pre->tree.poly, ctx);

  // Compute s_i's
  fast_evaluate(pre->s_points, pre->deriv, ctx, &pre->tree, n_points, pointsX);

  for(int i = 0; i < n_points; i++) {
    fmpz_invmod(pre->s_points[i], pre->s_points[i], modulus);
  }
  fmpz_mod_ctx_clear(ctx);
}

void poly_batch_precomp_init(struct precomp_s* const pre, char* modIn, const int n_points, char** pointsXin) {
  fmpz_init_from_gostr(pre->modulus, modIn);
  fmpz_mod_ctx_init(pre->ctx, pre->modulus);

  fmpz_t pointsX[n_points];
  for (int i = 0; i < n_points; i++) {
    fmpz_init_from_gostr(pointsX[i], pointsXin[i]);
  }

  c_precomp_init(pre, pre->modulus, n_points, pointsX);

  for (int i = 0; i < pre->n_points; i++) {
    fmpz_clear(pointsX[i]);
  }
}

void poly_batch_precomp_clear(struct precomp_s* const pre) {
  for (int i = 0; i < pre->n_points; i++) {
    fmpz_clear(pre->s_points[i]);
    fmpz_clear(pre->x_points[i]);
  }
  free(pre->s_points);
  free(pre->x_points);
  tree_clear(&pre->tree, pre->ctx);
  fmpz_mod_poly_clear(pre->deriv, pre->ctx);
  fmpz_mod_ctx_clear(pre->ctx);
}

void tree_clear(struct tree_s* const pre, const fmpz_mod_ctx_t ctx) {
  if (pre->left) {
    tree_clear(pre->left, ctx);
    free(pre->left);
  }
  if (pre->right) {
    tree_clear(pre->right, ctx);
    free(pre->right);
  }

  fmpz_mod_poly_clear(pre->poly, ctx);
}


static void fast_interpolate(fmpz_mod_poly_t poly, const fmpz_mod_ctx_t ctx, const struct precomp_s* const pre, const fmpz_t* const pointsY) {

  fmpz_t ys[pre->n_points];

  for(int i = 0; i < pre->n_points; i++) {
    fmpz_init(ys[i]);
    fmpz_mul(ys[i], pre->s_points[i], pointsY[i]);
    fmpz_mod(ys[i], ys[i], pre->modulus);
  }

  fast_linear_comp(poly, ctx, &pre->tree, pre->n_points, pre->x_points, ys);

  for(int i = 0; i < pre->n_points; i++)
    fmpz_clear(ys[i]);
}

static void fast_linear_comp(fmpz_mod_poly_t poly, const fmpz_mod_ctx_t ctx, const struct tree_s* const pre, const int n_points, fmpz_t* const pointsX, fmpz_t* const pointsY) {
  // This is Algorithm 10.9 from the book cited above.
  //
  // Input (x_1, ..., x_N)   and   (y_1, ..., y_N)
  // Output:
  //      SUM_i (y_i * m(x))/(x - x_i)
  // where m(x) = (x - x_1)(x - x_2)...(x - x_n)

  if (n_points == 1) {
    fmpz_mod_poly_zero(poly, ctx);
    fmpz_mod_poly_set_coeff_fmpz(poly, 0, pointsY[0], ctx);
    return;
  }

  const int k = n_points/2;

  fmpz_mod_poly_t r0, r1;
  fmpz_mod_poly_init(r0, ctx);
  fmpz_mod_poly_init(r1, ctx);

  fast_linear_comp(r0, ctx, pre->left, k, pointsX, pointsY);
  fast_linear_comp(r1, ctx, pre->right, n_points - k, pointsX + k, pointsY + k);

  fmpz_mod_poly_mul(r0, r0, pre->right->poly, ctx);
  fmpz_mod_poly_mul(r1, r1, pre->left->poly, ctx);

  fmpz_mod_poly_add(poly, r0, r1, ctx);

  fmpz_mod_poly_clear(r0, ctx);
  fmpz_mod_poly_clear(r1, ctx);
}


static void fast_evaluate(fmpz_t* const pointsY, const fmpz_mod_poly_t poly, const fmpz_mod_ctx_t ctx, const struct tree_s* const pre, const int n_points, const fmpz_t* const pointsX) {
  if (n_points == 1) {
    fmpz_mod_poly_get_coeff_fmpz(pointsY[0], poly, 0, ctx);
    return;
  }

  fmpz_mod_poly_t r0, r1;
  fmpz_mod_poly_init(r0, ctx);
  fmpz_mod_poly_init(r1, ctx);

  fmpz_mod_poly_rem(r0, poly, pre->left->poly, ctx);
  fmpz_mod_poly_rem(r1, poly, pre->right->poly, ctx);

  const int k = n_points/2;
  fast_evaluate(pointsY, r0, ctx, pre->left, k, pointsX);
  fast_evaluate(pointsY + k, r1, ctx, pre->right, n_points - k, pointsX + k);

  fmpz_mod_poly_clear(r0, ctx);
  fmpz_mod_poly_clear(r1, ctx);
}
