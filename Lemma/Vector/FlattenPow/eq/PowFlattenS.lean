import Lemma.Fin.Eq_Fin.of.EqVal
import Theorem.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Vector.GetFlatten_AddMul.eq.Get
import Lemma.Vector.GetPow.eq.PowGetS
open Vector Nat Fin


@[path]
private lemma main
  [HPow α β α]
-- given
  (a : List.Vector (List.Vector α n) m)
  (b : List.Vector (List.Vector β n) m) :
-- imply
  (a ^ b).flatten = a.flatten ^ b.flatten := by
-- proof
  ext k
  obtain ⟨i, j, h_eq⟩ := Fin.Any_Eq_AddMul.of.Lt_Mul k.isLt
  rw [Eq_Fin.of.EqVal h_eq]
  rw [GetPow.eq.PowGetS.fin]
  simp [GetFlatten_AddMul.eq.Get.fin]
  simp [GetPow.eq.PowGetS.fin]


-- created on 2026-08-23
-- updated on 2026-11-20
