import Mathlib.Analysis.SpecialFunctions.Exp
import sympy.Basic
open Filter Topology


@[main]
private lemma main
  {γ : ℝ}
-- given
  (h₀ : 0 < γ)
  (C c : ℝ) :
-- imply
  Tendsto (fun t : ℝ => C * Real.exp (-γ * t) * c) atTop (𝓝 0) := by
-- proof
  have h : Tendsto (fun t : ℝ => Real.exp (-γ * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  simpa using (h.const_mul C).mul_const c


-- created on 2026-09-26
