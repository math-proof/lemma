import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Tensor.EqHeadData
import Lemma.Fin.Eq_0
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
open Hyperreal Tensor Int Fin
set_option maxHeartbeats 1000000


@[main]
private lemma main
  {n : ℕ}
-- given
  (p : Fin n → Fin n → Bool)
  (A : Tensor ℝ [n, n]) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (p i j))
  let A : Tensor ℝ* [n, n] := A
  Exp.exp (A + (Ξ - 1) * ∞) ≈ exp A * Ξ := by
-- proof
  intro Ξ A'
  have h_A : A' = map Hyperreal.ofReal A := rfl
  apply Setoid.of.All_SetoidGetS.GtLength_0 (h := by simp)
  intro i
  apply Setoid.of.All_SetoidGetS.GtLength_0 (h := by simp)
  intro j
  simp
  have := GetExp.eq.ExpGet.fin (A' + (Ξ - 1) * ∞) ⟨i, by grind⟩
  simp at this
  rw [this]
  have := GetExp.eq.ExpGet.fin ((A' + (Ξ - 1) * ∞).get i) ⟨j, by grind⟩
  simp at this
  rw [this]
  have := GetAdd_MulSub_1.eq.Ite_Get.fin p A i j
  simp at this
  rw [← h_A] at this
  simp [Ξ]
  apply Setoid.of.SetoidDataS
  erw [DataExp.eq.ExpData]
  rw [GetAdd.eq.AddGetS.fin]
  erw [GetAdd.eq.AddGetS.fin]
  rw [GetMul.eq.MulGetS.fin]
  erw [GetMul.eq.MulGetS.fin ((Exp.exp A').get i) (([i<n][j<n]↑(p i j).toNat).get i) j]
  rw [GetMul.eq.MulGet.fin]
  erw [GetMul.eq.MulGet.fin (([i<n][j<n]((p i j).toNat : Tensor ℝ* []) - 1).get i) ω j]
  rw [GetSub.eq.SubGetS.fin]
  erw [GetSub.eq.SubGetS.fin (([i<n][j<n]↑(p i j).toNat).get i) (Tensor.get (1 : Tensor ℝ* [n, n]) i) j]
  repeat rw [EqGetStack.fn.fin]
  rw [EqGet1_1.fin]
  erw [EqGet1_1.fin (s := [n, n].tail) j (α := ℝ*)]
  rw [DataMul.eq.MulDataS]
  have := GetExp.eq.ExpGet.fin A' ⟨i, by grind⟩
  simp at this
  rw [this]
  have := GetExp.eq.ExpGet.fin (A'.get i) ⟨j, by grind⟩
  simp at this
  rw [this]
  erw [DataExp.eq.ExpData]
  rw [DataAdd.eq.AddDataS]
  rw [DataMul.eq.MulData]
  rw [DataSub.eq.SubDataS]
  rw [EqData1'1]
  rw [@Vector.MulSub.eq.SubMulS]
  apply @Vector.Setoid.of.All_SetoidGetS.fin
  intro k
  have h_k := Eq_0 k
  subst h_k
  rw [Vector.GetExp.eq.ExpGet.fin]
  erw [Vector.GetAdd.eq.AddGetS.fin]
  repeat rw [Tensor.DataGet.eq.GetUnflattenData.fin]
  erw [Vector.GetMul.eq.MulGetS.fin]
  erw [Vector.GetExp.eq.ExpGet.fin]
  repeat erw [Vector.GetUnflatten.eq.Get_AddMul.fin]
  erw [Vector.GetSub.eq.SubGetS.fin]
  repeat erw [Vector.GetMul.eq.MulGet.fin]
  erw [Vector.EqGet1_1.fin]
  simp
  erw [EqHeadData.nat]
  if h : p i j then
    simp [h]
  else
    simp [h]
    rw [Add_Neg.eq.Sub]
    apply SetoidExp_0.of.InfiniteNeg
    simp only [A', map]
    erw [Vector.GetMap.eq.UFnGet]
    apply InfiniteNegSub.of.InfinitePos _ InfinitePosInfty


-- created on 2025-12-05
-- updated on 2025-12-29
