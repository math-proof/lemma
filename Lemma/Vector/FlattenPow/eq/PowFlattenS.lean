import Lemma.Fin.Eq_Fin.of.EqVal
import Lemma.Nat.Any_Eq_AddMul
import Lemma.Vector.GetFlatten_AddMul.eq.Get
import Lemma.Vector.GetPow.eq.PowGetS
open Vector Nat Fin


@[main]
private lemma main
  [HPow α β α]
-- given
  (a : List.Vector (List.Vector α n) m)
  (b : List.Vector (List.Vector β n) m) :
-- imply
  (a ^ b).flatten = a.flatten ^ b.flatten := by
-- proof
  ext k
  obtain ⟨i, j, h_eq⟩ := Any_Eq_AddMul k
  rw [Eq_Fin.of.EqVal h_eq]
  rw [GetPow.eq.PowGetS.fin]
  simp [GetFlatten_AddMul.eq.Get.fin]
  simp [GetPow.eq.PowGetS.fin]


-- created on 2026-08-23
-- updated on 2026-08-24
