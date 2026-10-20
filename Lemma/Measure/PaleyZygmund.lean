import Mathlib
import sympy.Basic
import sympy.atlas.Probability.PaleyZygmund
open MeasureTheory
open scoped ENNReal
open ProbabilityTheory


/--
[paley_zygmund](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/PaleyZygmund.lean)
-/
@[path]
private lemma paley_zygmund_eq
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Z : Ω → ℝ}
  {θ : ℝ}
-- given
  (hZ_nn : 0 ≤ᵐ[μ] Z)
  (hZ2 : MemLp Z 2 μ)
  (hθ0 : 0 ≤ θ)
  (hθ1 : θ ≤ 1) :
-- imply
  (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 ≤
    (∫ ω, Z ω ^ 2 ∂μ) * μ.real {ω | θ * ∫ ω, Z ω ∂μ < Z ω} := by
-- proof
  apply ProbabilityTheory.paley_zygmund hZ_nn hZ2 hθ0 hθ1


-- created on 2026-10-20
