import Mathlib
import sympy.Basic


private lemma mul_basis_eq_sum
  [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
  {b : Module.Basis ι R A} {c : A} {j : ι} :
-- imply
  c * b j = ∑ k, Algebra.leftMulMatrix b c k j • b k := by
-- proof
  conv_lhs => rw [← b.sum_repr (c * b j)]
  simp only [Algebra.leftMulMatrix_eq_repr_mul]

private lemma of_dual_mul_mul_eq
  [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
  {b : Module.Basis ι R A} {τ : Module.Dual R A} {c : A} :
-- imply
  (Matrix.of fun i j => τ (c * b i * b j)) =
    (Algebra.leftMulMatrix b c).transpose * Matrix.of fun i j => τ (b i * b j) := by
-- proof
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [mul_basis_eq_sum (c := c) (j := i), Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]


/--
[Algebra_det_dual_mul_mul_eq_norm_mul_det](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_det_dual_mul_mul_eq_norm_mul_det.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
  {b : Module.Basis ι R A} {τ : Module.Dual R A} {c : A} :
-- imply
  (Matrix.of fun i j => τ (c * b i * b j)).det =
    Algebra.norm R c * (Matrix.of fun i j => τ (b i * b j)).det := by
-- proof
  rw [of_dual_mul_mul_eq, Matrix.det_mul, Matrix.det_transpose, Algebra.norm_eq_matrix_det b]


-- created on 2026-10-13
