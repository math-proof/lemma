import Lemma.Nat.Eq_0.of.Lt_1
import Lemma.Nat.Eq_Mk.of.EqVal
import Lemma.Nat.LtVal
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.EqFlattenMapRange.of.All_EqGetUnflatten
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import sympy.vector.vector
open Nat Vector


@[main]
private lemma main
  {u : Fin 1 → List.Vector α n} :
-- imply
  ((List.Vector.range 1).map fun i => u i).flatten = cast (by simp) (u 0) := by
-- proof
  apply EqFlattenMapRange.of.All_EqGetUnflatten
  intro t
  have h_t := LtVal t
  have h_t := Eq_0.of.Lt_1 h_t
  have h_t := Eq_Mk.of.EqVal h_t
  simp [h_t]
  apply Eq.of.All_EqGetS
  intro i
  simp only [GetElem.getElem]
  rw [GetUnflatten.eq.Get_AddMul.fin]
  simp [GetCast.eq.Get.of.Eq.fin]


-- created on 2025-11-11
