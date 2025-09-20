import Lemma.Algebra.Eq.of.All_EqGetS
import Lemma.Algebra.Get.eq.Zero
open Algebra


@[main]
private lemma main
  [GroupWithZero α]
-- given
  (n : ℕ) :
-- imply
  (0 : List.Vector α n) / (0 : List.Vector α n) = (0 : List.Vector α n) := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [Get.eq.Zero]
  simp [HDiv.hDiv]
  simp [Div.div]
  simp [GetElem.getElem]
  rw [Get.eq.Zero.fin]


-- created on 2025-09-04
