import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Nat.Eq_0.of.Lt_1
import Lemma.Fin.Eq_Fin.of.EqVal
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.EqFlattenMapRange.of.All_EqGetUnflatten
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
open Nat Vector Fin Bool


@[main, cast]
private lemma main
  (u : Fin 1 → List.Vector α n) :
-- imply
  ((List.Vector.range 1).map fun i => u i).flatten ≃ u 0 := by
-- proof
  apply SEq.of.Eq_Cast (h := by simp)
  apply EqFlattenMapRange.of.All_EqGetUnflatten
  intro t
  have h_t := t.isLt
  have h_t := Eq_0.of.Lt_1 h_t
  have h_t := Eq_Fin.of.EqVal h_t
  simp [h_t]
  apply Eq.of.All_EqGetS
  intro i
  simp only [GetElem.getElem]
  rw [GetUnflatten.eq.Get_AddMul.fin]
  simp [GetCast.eq.Get.of.Eq.fin]


-- created on 2025-11-11
