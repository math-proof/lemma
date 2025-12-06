import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Mul
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.MulMapS.eq.Map_FunMul
import sympy.tensor.stack
open Nat Vector Fin


@[main]
private lemma main
  [Mul α]
-- given
  (X : Tensor α (s₀ :: s))
  (a : α) :
-- imply
  ([i < s₀] X[i]) * a = [i < s₀] X[i] * a := by
-- proof
  unfold Stack Tensor.fromVector
  simp only [HMul.hMul]
  simp
  ext t
  have h_t := t.isLt
  let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
  simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]


-- created on 2025-12-06
