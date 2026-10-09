import Mathlib
import sympy.Basic


/--
[Matrix_det_eq_zero_of_isIdempotentElem_of_trace_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_det_eq_zero_of_isIdempotentElem_of_trace_eq_one.lean)
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
  {e : Matrix (Fin 2) (Fin 2) A}
-- given
  (he : IsIdempotentElem e)
  (htr : e.trace = 1) :
-- imply
  e.det = 0 := by
-- proof
  have hch := w2aux_mul_self_eq e
  rw [he.eq, htr, one_smul] at hch
  have h0 : e.det • (1 : Matrix (Fin 2) (Fin 2) A) = 0 := sub_eq_self.mp hch.symm
  have h00 := congrFun (congrFun h0 0) 0
  simpa using h00


-- created on 2026-10-05
