import stdlib.List.Vector
import Lemma.Logic.EqCast.of.Eq
import Lemma.Algebra.Eq.of.All_EqGetS.Eq
import Lemma.Algebra.EqMin.of.Le
import Lemma.Algebra.EqGetRange.of.Lt
import Lemma.Algebra.GetTake.eq.Get.of.Lt_Min
import Lemma.Algebra.GetDrop.eq.Get_Add.of.Lt_Sub
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Logic.EqCast.of.SEq
open Algebra Logic Vector


@[main]
private lemma main
  {s : List ℕ}
-- given
  (v : List.Vector α s.prod) :
-- imply
  (v.splitAt 0)[0] = v := by
-- proof
  unfold List.Vector.splitAt
  simp
  unfold List.Vector.unflatten
  simp
  unfold List.Vector.array_slice
  simp
  apply EqCast.of.SEq
  apply Eq.of.All_EqGetS.Eq
  ·
    intro i
    simp [GetTake.eq.Get.of.Lt_Min]
    rw [GetDrop.eq.Get_Add.of.Lt_Sub]
    simp
    rw [GetCast.eq.Get.of.Eq.Lt]
    simp
  ·
    rw [EqMin.of.Le]
    rw [EqGetRange.of.Lt]
    simp


@[main]
private lemma fin
  {s : List ℕ}
-- given
  (v : List.Vector α s.prod) :
-- imply
  (v.splitAt 0).get ⟨0, by simp⟩ = v := by
-- proof
  have := main v
  simp [GetElem.getElem] at this
  assumption


-- created on 2025-07-12
