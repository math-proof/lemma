import Lemma.Hyperreal.Sub_Infty.to.NegInfty
import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Nat.Eq_0
import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.EqData1'1
import Lemma.Tensor.EqGet1_1
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.EqMul0_0
import Lemma.Tensor.GetAdd.eq.AddGetS
import Lemma.Tensor.GetData.eq.GetDataGet.of.Lt
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.GetMul.eq.MulGet.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.GetSub.eq.SubGetS
import Lemma.Tensor.GetSubStackBool.eq.One
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Setoid.is.SetoidDataS
import Lemma.Vector.EqGet1_1
import Lemma.Vector.GetAdd.eq.AddGetS
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetNeg.eq.NegGet
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.Head.eq.Get_0
import Lemma.Vector.Setoid.is.All_SetoidGetS
import sympy.tensor.functions
import sympy.tensor.stack
open Hyperreal Int Nat Tensor Vector


@[main]
private lemma main
  {n : ℕ}
-- given
  (p : Fin n → Fin n → Bool)
  (A : Tensor ℝ [n, n])
  (i j : Fin n) :
-- imply
  let mask : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (p i j))
  let A : Tensor ℝ* [n, n] := A
  (A + (mask - 1) * Hyperreal.omega)[i, j] ≈ if p i j then
    A[i, j]
  else
    (-Hyperreal.omega : Tensor ℝ* []) := by
-- proof
  intro mask
  simp [GetElem.getElem]
  repeat rw [@Tensor.GetAdd.eq.AddGetS.fin]
  have := GetMul.eq.MulGet.of.Lt_Get_0.GtLength_0.fin (by grind) (by grind) (mask - 1) Hyperreal.omega (i := i)
  simp at this
  rw [this]
  simp
  have := GetMul.eq.MulGet.of.Lt_Get_0.GtLength_0.fin (by grind) (by grind) ((mask - 1).get i) Hyperreal.omega (i := j)
  simp at this
  rw [this]
  split_ifs with h_p
  ·
    rw [GetSub.eq.SubGetS.fin]
    have := EqGet1_1.fin (i := ⟨i, by simp [Length.eq.Get_0.of.GtLength_0]⟩) (s := [n, n]) (α := ℝ*)
    simp at this
    rw [this]
    rw [GetSub.eq.SubGetS.fin]
    have := EqGet1_1.fin (i := ⟨j, by simp [Length.eq.Get_0.of.GtLength_0]⟩) (s := [n, n].tail) (α := ℝ*)
    simp at this
    rw [this]
    simp [mask]
    repeat rw [EqGetStack.fn.fin]
    simp [h_p]
    simp [@Tensor.EqMul0_0]
  ·
    have := GetMap.eq.MapGet A Hyperreal.ofReal (i := ⟨i, by simp [Tensor.length]⟩)
    simp at this
    rw [this]
    have := GetMap.eq.MapGet (A.get i) Hyperreal.ofReal (i := ⟨j, by simp [Tensor.length]⟩)
    simp at this
    rw [this]
    simp [Tensor.map]
    apply Setoid.of.SetoidDataS
    rw [DataAdd.eq.AddDataS]
    simp [DataNeg.eq.NegData]
    rw [DataMul.eq.MulData]
    apply Setoid.of.All_SetoidGetS.fin
    intro k
    rw [@Vector.GetAdd.eq.AddGetS.fin]
    rw [@Vector.GetNeg.eq.NegGet.fin]
    simp
    rw [@Vector.GetMul.eq.MulGet.fin]
    have h_k := Eq_0 k
    subst h_k
    have := GetData.eq.GetDataGet.of.Lt.fin (i := j) (by simp) (A.get i)
    simp [GetElem.getElem] at this
    rw [Head.eq.Get_0.fin] at this
    rw [← this]
    rw [GetSubStackBool.eq.One]
    simp [h_p]
    rw [DataGet.eq.GetUnflattenData.fin A i]
    rw [GetUnflatten.eq.Get_AddMul.fin]
    simp
    rw [DataNeg.eq.NegData]
    rw [EqData1'1]
    rw [Head.eq.Get_0.fin]
    rw [@Vector.GetNeg.eq.NegGet.fin]
    rw [@Vector.EqGet1_1.fin]
    simp [Add_Neg.eq.Sub]
    simp [List.Vector.head]
    apply Sub_Infty.to.NegInfty


@[main]
private lemma fin
  {n : ℕ}
-- given
  (p : Fin n → Fin n → Bool)
  (A : Tensor ℝ [n, n])
  (i j : Fin n) :
-- imply
  let mask : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (p i j))
  let A : Tensor ℝ* [n, n] := A
  ((A + (mask - 1) * Hyperreal.omega).get i).get j ≈ if p i j then
    (A.get i).get j
  else
    (-Hyperreal.omega : Tensor ℝ* []) := by
-- proof
  apply main


-- created on 2025-12-06
-- updated on 2025-12-23
