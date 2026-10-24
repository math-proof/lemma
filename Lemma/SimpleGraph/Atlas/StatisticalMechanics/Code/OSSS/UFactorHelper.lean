import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.UFactorHelper
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[ofh_factor_one_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/UFactorHelper.lean)
-/
@[path]
private lemma ofh_factor_one_component_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {G : (Fin n → ℝ) → ℝ}
  {CG : ℝ}
-- given
  (hGm : Measurable G)
  (hGC : ∀ U, |G U| ≤ CG) :
-- imply
  (∫ U, truncInd μ σ f U (t + 1) * G U ∂(cube n)) = ∫ A, acp_truncHead μ σ f t A * (∫ B, G (acp_join t A B) ∂(ubfTail n t)) ∂(ubfHead n t) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.ofh_factor_one_component μ σ f t hGm hGC


-- created on 2026-10-23
