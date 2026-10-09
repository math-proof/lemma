import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Exp


@[path]
private lemma attention_free
  {T d : ℕ}
  {Q K V : Fin T → Fin d → ℝ} :
-- imply
  (fun t c => (1 + Real.exp (-Q t c))⁻¹ * ∑ i, V i c * (Real.exp (K i c) / ∑ j, Real.exp (K j c))) =
    fun t c => (1 + Real.exp (-Q t c))⁻¹ * ∑ i, Real.exp (K i c) / (∑ j, Real.exp (K j c)) * V i c := by
-- proof
  funext t c
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _


-- created on 2026-09-27
