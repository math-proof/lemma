import Lemma.Fin.All_EqUFnS.of.All_Eq
import Lemma.Nat.EqMod_1'0
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.EqStackS.of.All_Eq
import Lemma.Tensor.EqStack_Get
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.Mul_Stack.eq.Stack_Mul
import Lemma.Tensor.Mul_SumStack.eq.SumStack_Mul
open Fin Nat Tensor


@[main, comm]
private lemma main
  [NonUnitalNonAssocSemiring α]
-- given
  (X : Tensor α (n :: s))
  (A : Tensor α s) :
-- imply
  let S : Tensor α s := X.sum 0
  A * S = (cast (congrArg (Tensor α) (by simp)) ((A.unsqueeze 0).repeat ⟨0, by grind⟩ n) * X).sum 0 := by
-- proof
  simp
  have h_X := EqStack_Get.fin X
  rw [← h_X]
  have h_s : (s.insertIdx 0 1).set 0 (n * (s.insertIdx 0 1)[0]) = n :: s := by
    simp
  have h_mul_stack := Mul_Stack.eq.Stack_Mul.fin (cast (congrArg (Tensor α) h_s) ((A.unsqueeze 0).repeat ⟨0, by grind⟩ n)) (fun i => X[i])
  simp [GetElem.getElem] at h_mul_stack
  have h_all : ∀ i : Fin n, (cast (congrArg (Tensor α) h_s) ((A.unsqueeze 0).repeat ⟨0, by grind⟩ n)).get i = A := by
    intro i
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (s' := n :: s) (i := ⟨i, by grind⟩) (by grind) (by grind)]
    simp
    erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
    simp [EqMod_1'0]
    erw [EqGetUnsqueeze_0.fin]
  have h_all := All_EqUFnS.of.All_Eq.bin h_all (f := fun a i => a * X.get i)
  erw [EqStackS.of.All_Eq.fin h_all] at h_mul_stack
  conv_rhs =>
    arg 1
    erw [h_mul_stack]
  apply Mul_SumStack.eq.SumStack_Mul


-- created on 2026-07-22
