import Mathlib
import sympy.Basic
import Structure.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part3
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WavefrontSet
open scoped SchwartzMap FourierTransform


namespace WavefrontSet

/--
[wfsc_decomposition_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ScatteringWavefront.lean)
-/
@[path]
lemma wfsc_decomposition_iff
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p q : ClosedBall n}
-- given
  (hpq : (p, q) ∈ BoundaryProd n) :
-- imply
  (p, q) ∉ WFsc u ↔ ∃ u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ), u = u₁ + u₂ ∧ p ∉ Css u₁ ∧ q ∉ Css (𝓕 u₂) :=
-- proof
  not_mem_wfsc_iff_exists_decomp hpq

end WavefrontSet


-- created on 2026-10-23
