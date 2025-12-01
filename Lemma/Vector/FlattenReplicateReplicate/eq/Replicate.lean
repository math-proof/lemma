import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import sympy.vector.vector
open Nat Vector Fin


@[main]
private lemma main
-- given
  (m n : ℕ)
  (x : α) :
-- imply
  (List.Vector.replicate m (List.Vector.replicate n x)).flatten = List.Vector.replicate (m * n) x := by
-- proof
  ext t
  have h_t := t.isLt
  let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
  simp


-- created on 2025-11-30
