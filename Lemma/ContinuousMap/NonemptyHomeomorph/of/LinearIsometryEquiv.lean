import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.NormedSpace.BanachStone

/--
[BanachStone](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/BanachStone.lean)
-/
@[path]
private lemma banachStone_real_is
-- given
  {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  (e : LinearIsometryEquiv (RingHom.id ℝ) (ContinuousMap X ℝ) (ContinuousMap Y ℝ)) :
-- imply
  Nonempty (Homeomorph X Y) := by
-- proof
  apply FunctionalAnalysis.BanachStoneWanted.banachStone_real e

-- created on 2026-10-10
