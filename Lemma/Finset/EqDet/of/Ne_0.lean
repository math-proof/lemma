import sympy.sets.sets
import sympy.Basic
open Matrix


@[main]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℂ}
-- given
  (_h : A.det ≠ 0) :
-- imply
  (A.det)⁻¹ • A.adjugate = A⁻¹ := by
-- proof
  rw [Matrix.inv_def, Ring.inverse_eq_inv']


-- created on 2020-02-12
