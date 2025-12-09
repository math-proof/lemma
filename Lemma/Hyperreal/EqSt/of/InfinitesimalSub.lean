import Lemma.Hyperreal.IsSt.is.All_LtAbs
import Lemma.Int.LtAbsSub.is.LtSub.Lt_Add
open Hyperreal Int


@[main]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h : Infinitesimal (x - r)) :
-- imply
  st x = r := by
-- proof
  unfold Infinitesimal at h
  simp [IsSt.is.All_LtAbs] at h
  apply IsSt.st_eq
  simp [IsSt]
  intro δ h_δ
  rw [← LtAbsSub.is.LtSub.Lt_Add]
  apply h δ h_δ


-- created on 2025-12-09
