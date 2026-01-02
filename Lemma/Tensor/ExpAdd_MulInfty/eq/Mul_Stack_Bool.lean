import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Tensor.EqHeadData
import Lemma.Nat.Eq_0
import Lemma.Vector.MulSub.eq.SubMulS
import Lemma.Tensor.DataSub.eq.SubDataS
import Lemma.Hyperreal.InfinitePos.is.InfiniteNegSub
import Lemma.Hyperreal.InfinitePosInfty
import Lemma.Hyperreal.InfiniteNeg.is.SetoidExp_0
import Lemma.Hyperreal.InfinitePos.is.InfiniteNegNeg
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetAdd_MulSub_1.eq.Ite_Get
import Lemma.Tensor.GetExp.eq.ExpGet
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.Setoid.is.All_SetoidGetS.of.GtLength_0
import Lemma.Tensor.Setoid.is.SetoidDataS
import Lemma.Tensor.SetoidExpS.of.Setoid_0
import Lemma.Vector.EqGet0_0
import Lemma.Vector.GetExp.eq.ExpGet
import sympy.tensor.functions
import sympy.tensor.stack
open Hyperreal Tensor Nat Int


@[main]
private lemma main
  {n : ℕ}
-- given
  (p : Fin n → Fin n → Bool)
  (A : Tensor ℝ [n, n]) :
-- imply
  let mask : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (p i j))
  let A : Tensor ℝ* [n, n] := A
  Exp.exp (A + (mask - 1) * Hyperreal.omega) ≈ exp A * mask := by
-- proof
  intro mask A'
  have h_A : A' = map Hyperreal.ofReal A := rfl
  apply Setoid.of.All_SetoidGetS.GtLength_0 (h := by simp)
  intro i
  apply Setoid.of.All_SetoidGetS.GtLength_0 (h := by simp)
  intro j
  simp
  have := GetExp.eq.ExpGet.fin (A' + (mask - 1) * Hyperreal.omega) ⟨i, by grind⟩
  simp at this
  rw [this]
  have := GetExp.eq.ExpGet.fin ((A' + (mask - 1) * Hyperreal.omega).get i) ⟨j, by grind⟩
  simp at this
  rw [this]
  have := GetAdd_MulSub_1.eq.Ite_Get.fin p A i j
  simp at this
  rw [← h_A] at this
  simp [mask]
  apply Setoid.of.SetoidDataS
  rw [DataExp.eq.ExpData]
  repeat rw [GetAdd.eq.AddGetS.fin]
  repeat rw [GetMul.eq.MulGetS.fin]
  repeat rw [GetMul.eq.MulGet.fin]
  repeat rw [GetSub.eq.SubGetS.fin]
  repeat rw [EqGetStack.fn.fin]
  repeat rw [EqGet1_1.fin]
  rw [DataMul.eq.MulDataS]
  have := GetExp.eq.ExpGet.fin A' ⟨i, by grind⟩
  simp at this
  rw [this]
  have := GetExp.eq.ExpGet.fin (A'.get i) ⟨j, by grind⟩
  simp at this
  rw [this]
  rw [DataExp.eq.ExpData]
  rw [DataAdd.eq.AddDataS]
  rw [DataMul.eq.MulData]
  rw [DataSub.eq.SubDataS]
  rw [EqData1'1]
  rw [@Vector.MulSub.eq.SubMulS]
  apply @Vector.Setoid.of.All_SetoidGetS.fin
  intro k
  have h_k := Eq_0.prod k
  subst h_k
  rw [Vector.GetExp.eq.ExpGet.fin]
  rw [Vector.GetAdd.eq.AddGetS.fin]
  repeat rw [Tensor.DataGet.eq.GetUnflattenData.fin]
  rw [Vector.GetMul.eq.MulGetS.fin]
  rw [Vector.GetExp.eq.ExpGet.fin]
  repeat rw [Vector.GetUnflatten.eq.Get_AddMul.fin]
  rw [Vector.GetSub.eq.SubGetS.fin]
  repeat rw [Vector.GetMul.eq.MulGet.fin]
  rw [Vector.EqGet1_1.fin]
  simp [EqHeadData.nat]
  if h : p i j then
    simp [h]
  else
    simp [h]
    rw [Add_Neg.eq.Sub]
    apply SetoidExp_0.of.InfiniteNeg
    simp [A', map]
    apply InfiniteNegSub.of.InfinitePos _ InfinitePosInfty


-- created on 2025-12-05
-- updated on 2025-12-29
