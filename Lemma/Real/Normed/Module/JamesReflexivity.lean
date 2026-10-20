import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Normed.Module.JamesReflexivity
open Set Metric
open Filter
open MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted


/--
[_root_.NormedSpace.goldstine_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Module/JamesReflexivity.lean)
-/
@[path]
private lemma NormedSpace_goldstine_finite_eq
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  {T : StrongDual ℝ (StrongDual ℝ X)}
  {s : Finset (StrongDual ℝ X)}
  {ε : ℝ}
-- given
  (hT : ‖T‖ ≤ 1)
  (hε : 0 < ε) :
-- imply
  ∃ x : X, ‖x‖ ≤ 1 ∧ ∀ z ∈ s, |z x - T z| < ε := by
-- proof
  apply NormedSpace.goldstine_finite T hT s hε

/--
[james_reflexivity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Module/JamesReflexivity.lean)
-/
@[path]
private lemma james_reflexivity_eq
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
-- imply
  Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E)
    ↔ ∀ f : StrongDual 𝕜 E, ∃ x ∈ Metric.closedBall (0 : E) 1, ‖f x‖ = ‖f‖ := by
-- proof
  apply MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted.james_reflexivity


-- created on 2026-10-20
