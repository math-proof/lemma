import Lemma.Hyperreal.IsSt.is.All_LtAbs
import Lemma.Int.LtAbsSub.is.LtSub.Lt_Add
open Hyperreal Int


@[main]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h_x : ¬Infinite x)
  (h_st : st x = r) :
-- imply
  Infinitesimal (x - r) := by
-- proof
  unfold Infinitesimal
  rw [← h_st]
  apply Hyperreal.infinitesimal_sub_st h_x

-- created on 2025-12-09
