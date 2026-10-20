import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.CorrectedRosenbloom
open MeasureTheory ProbabilityTheory Set
open Complex


/--
[wimanMajorant_le_eight_mul_maximumTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CorrectedRosenbloom.lean)
-/
@[path]
private lemma wimanMajorant_le_eight_mul_maximumTerm_eq
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  wimanMajorant f (Real.exp x) ≤
    8 * wimanMaximumTerm f (Real.exp x) *
    (1 + Real.sqrt (iteratedDeriv 2 (wimanGrowth f) x)) := by
-- proof
  apply Complex.wimanMajorant_le_eight_mul_maximumTerm f hf x


-- created on 2026-10-20
