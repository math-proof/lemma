import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.NormedSpace.KreinSmulian.Part4

/--
[KreinSmulian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/KreinSmulian.lean)
-/
@[path]
private lemma krein_smulian_iff
-- given
  {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {s : Set (WeakDual 𝕜 E)}
  (hs : Convex ℝ s) :
-- imply
  IsClosed s ↔
    ∀ (r : ℝ) (_ : 0 < r),
      IsClosed (s ∩ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r) := by
-- proof
  apply FunctionalAnalysis.BanachSpaceWanted.krein_smulian hs

-- created on 2026-10-10
