import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Eq_Fin.of.EqVal
import Lemma.Vector.EqGetReplicate
import Lemma.Vector.GetFlatten_AddMul.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import stdlib.SEq
open Fin Nat Vector


@[main]
private lemma main
-- given
  (x : List.Vector α n) :
-- imply
  x.repeat 1 ≃ x := by
-- proof
  unfold List.Vector.repeat
  apply SEq.of.All_EqGetS.Eq.fin
  ·
    intro t
    have h_t := t.isLt
    let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
    have h_qr := Eq_Fin.of.EqVal h_qr
    rw [h_qr]
    rw [GetFlatten_AddMul.eq.Get.fin]
    rw [EqGetReplicate]
    simp
  ·
    simp


-- created on 2026-01-10
