import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGet1_1
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetAdd.eq.AddGetS
import Lemma.Tensor.GetMul.eq.MulGet.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.GetSub.eq.SubGetS
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Mul.eq.Zero.of.Eq_0
import sympy.core.relational
import sympy.tensor.functions
import sympy.tensor.stack
open Tensor


@[main]
private lemma main
  {n : ℕ}
-- given
  (p : Fin n → Fin n → Bool)
  (A : Tensor ℝ* [n, n])
  (i j : Fin n) :
-- imply
  let mask : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (p i j))
  (A + (mask - 1) * Hyperreal.omega)[i, j] = if p i j then
    A[i, j]
  else
    (-Hyperreal.omega : Tensor ℝ* []) := by
-- proof
  intro mask
  denote h_A : A' = A + (mask - 1) * Hyperreal.omega
  simp [GetElem.getElem]
  repeat rw [GetAdd.eq.AddGetS.fin]
  have := GetMul.eq.MulGet.of.Lt_Get_0.GtLength_0.fin (by grind) (by grind) (mask - 1) Hyperreal.omega (i := i)
  simp at this
  rw [this]
  simp
  have := GetMul.eq.MulGet.of.Lt_Get_0.GtLength_0.fin (by grind) (by grind) ((mask - 1).get i) Hyperreal.omega (i := j)
  simp at this
  rw [this]
  split_ifs with h_p
  ·
    simp
    apply Mul.eq.Zero.of.Eq_0
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
  ·
    sorry


-- created on 2025-12-06
-- updated on 2025-12-08
