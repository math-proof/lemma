import Lemma.Hyperreal.GtInfty0
import Lemma.Hyperreal.Infinite.is.All_GtAbs
import Lemma.Int.EqAbs.of.Gt_0
open Hyperreal Int


@[main]
private lemma main :
-- imply
  Hyperreal.omega.Infinite := by
-- proof
  apply Infinite.of.All_GtAbs
  intro ⟨δ, hδ⟩
  simp [EqAbs.of.Gt_0 GtInfty0]
  refine infinitePos_def.mp (infinitePos_of_tendsto_top tendsto_natCast_atTop_atTop) δ


-- created on 2025-12-16
