import Lemma.Hyperreal.GtInfty0
import Lemma.Hyperreal.Infinite.is.All_GtAbs
import Lemma.Int.EqAbs.of.Gt_0
open Hyperreal Int


@[main]
private lemma main :
-- imply
  Hyperreal.omega → ∞ := by
  apply Infinite.of.All_GtAbs
  intro ⟨δ, hδ⟩
  simp [EqAbs.of.Gt_0 GtInfty0]
  exact coe_lt_omega δ


-- created on 2025-12-16
