import Mathlib
import sympy.Basic
import sympy.atlas.Probability.CramerDecomposition
open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.CramerDecompositionWanted


/--
[cramer_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/CramerDecomposition.lean)
-/
@[path]
private lemma cramer_decomposition_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X Y : Ω → ℝ}
-- given
  (hX : Measurable X)
  (hY : Measurable Y)
  (hXY : IndepFun X Y μ)
  (hAdd : HasGaussianLaw (fun ω => X ω + Y ω) μ) :
-- imply
  HasGaussianLaw X μ ∧ HasGaussianLaw Y μ := by
-- proof
  apply MathlibExt.Probability.CramerDecompositionWanted.cramer_decomposition hX hY hXY hAdd


-- created on 2026-10-20
