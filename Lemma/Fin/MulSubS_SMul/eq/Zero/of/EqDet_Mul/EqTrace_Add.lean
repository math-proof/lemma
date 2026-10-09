import Mathlib
import sympy.Basic


/--
[Matrix_sub_smul_one_mul_sub_smul_one_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_sub_smul_one_mul_sub_smul_one_eq_zero.lean)
-/

private lemma  w2aux_mul_self_eq {A : Type*} [CommRing A] (M : Matrix (Fin 2) (Fin 2) A) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) A) := by
  rw [← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne, ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true,
    Fin.one_eq_zero_iff, mul_zero, mul_one]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring
@[path]
private lemma main
  [CommRing A]
  {M : Matrix (Fin 2) (Fin 2) A}
  {a b : A}
-- given
  (htr : M.trace = a + b)
  (hdet : M.det = a * b) :
-- imply
  (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) * (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) = 0 := by
-- proof
  have h := w2aux_mul_self_eq M
  rw [htr, hdet] at h
  have e1 : M * (b • (1 : Matrix (Fin 2) (Fin 2) A)) = b • M := by rw [mul_smul_comm, mul_one]
  have e2 : (a • (1 : Matrix (Fin 2) (Fin 2) A)) * M = a • M := by rw [smul_mul_assoc, one_mul]
  have e3 : (a • (1 : Matrix (Fin 2) (Fin 2) A)) * (b • (1 : Matrix (Fin 2) (Fin 2) A)) =
      (a * b) • (1 : Matrix (Fin 2) (Fin 2) A) := by
    rw [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul]
  rw [sub_mul, mul_sub, mul_sub, h, e1, e2, e3, add_smul]
  abel


-- created on 2026-10-05
