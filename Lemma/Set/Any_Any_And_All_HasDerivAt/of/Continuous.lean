import Mathlib
import sympy.Basic
import Theorem.Analysis.ODE.CauchyPeano

/--
[CauchyPeano](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/CauchyPeano.lean)
-/
@[path]
private lemma cauchy_peano_exists_is
-- given
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (f : ℝ × E → E)
  (hf : Continuous f)
  (t₀ : ℝ)
  (x₀ : E) :
-- imply
  ∃ ε > 0, ∃ x : ℝ → E, x t₀ = x₀ ∧
    ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), HasDerivAt x (f (t, x t)) t := by
-- proof
  apply ODE.CauchyPeanoWanted.cauchy_peano_exists f hf t₀ x₀

-- created on 2026-10-10
