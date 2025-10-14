import stdlib.List
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.LeMod.of.Gt_0
import Lemma.Nat.EqAddSub.of.Ge
open Nat


@[main]
private lemma main
-- given
  (v : List α)
  (i : ℕ) :
-- imply
  (v.rotate i).length = v.length := by
-- proof
  unfold List.rotate
  simp
  by_cases h : v.length = 0
  ·
    simp [h]
  ·
    have := LeMod.of.Gt_0 (by omega) i (d := v.length)
    rw [EqMin.of.Le this]
    rwa [EqAddSub.of.Ge]


-- created on 2025-10-14
