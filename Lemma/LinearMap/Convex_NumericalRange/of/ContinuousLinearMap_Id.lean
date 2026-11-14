import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.InnerProductSpace.ToeplitzHausdorff

open InnerProductSpace.ToeplitzHausdorffWanted


/--
[ToeplitzHausdorff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/ToeplitzHausdorff.lean)
-/
@[path]
private lemma toeplitz_hausdorff_general_is
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (A : ContinuousLinearMap (RingHom.id ℂ) E E) :
-- imply
  Convex ℝ (numericalRange A) := by
-- proof
  apply InnerProductSpace.ToeplitzHausdorffWanted.toeplitz_hausdorff_general A

/--
[ToeplitzHausdorff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/ToeplitzHausdorff.lean)
-/
@[path]
private lemma toeplitz_hausdorff_is
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (A : ContinuousLinearMap (RingHom.id ℂ) E E) :
-- imply
  Convex ℝ (numericalRange A) := by
-- proof
  apply InnerProductSpace.ToeplitzHausdorffWanted.toeplitz_hausdorff A

-- created on 2026-10-10
