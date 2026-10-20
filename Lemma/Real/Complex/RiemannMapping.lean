import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.RiemannMapping
open Filter Metric Set
open scoped Topology
open MathlibExt.Analysis.Complex.RiemannMappingWanted


/--
[riemannMapping_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/RiemannMapping.lean)
-/
@[path]
private lemma riemannMapping_normalized_eq
  {U : Set ℂ}
  {z₀ : ℂ}
-- given
  (hUo : IsOpen U)
  (hUc : IsSimplyConnected U)
  (hU : U ≠ Set.univ)
  (hz₀ : z₀ ∈ U) :
-- imply
  ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ Set.BijOn f U (Metric.ball (0 : ℂ) 1) ∧
    f z₀ = 0 ∧ (deriv f z₀).im = 0 ∧ 0 < (deriv f z₀).re ∧
    ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U → Set.BijOn g U (Metric.ball (0 : ℂ) 1) →
    g z₀ = 0 → (deriv g z₀).im = 0 → 0 < (deriv g z₀).re →
    Set.EqOn f g U := by
-- proof
  apply MathlibExt.Analysis.Complex.RiemannMappingWanted.riemannMapping_normalized hUo hUc hU hz₀


-- created on 2026-10-20
