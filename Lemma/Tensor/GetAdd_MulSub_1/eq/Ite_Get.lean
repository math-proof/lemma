import Lemma.Tensor.Eq_TensorReplicate
import Lemma.Int.Sub.eq.Zero.is.Eq
import Lemma.Int.Sub0.eq.Neg
import Lemma.Hyperreal.XEq.of.Eq
import Lemma.Nat.Sub.eq.Zero
import Lemma.Hyperreal.Sub_Infty.to.NegInfty
import Lemma.Tensor.EqGet1_1
import Lemma.Tensor.EqMul0_0
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.GetMul.eq.MulGet
import Lemma.Tensor.GetSub.eq.SubGetS
import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Vector.XEq.is.All_XEqGetS
open Hyperreal Int Tensor Vector
set_option maxHeartbeats 2000000


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GetAdd_MulSub_1.eq.Ite_Get |
| fin | Tensor.GetAdd_MulSub_1.eq.Ite_Get.fin |
-/
@[main, fin]
private lemma main
  {n : ℕ}
-- given
  (p : Fin n → Fin n → Bool)
  (A : Tensor ℝ [n, n])
  (i j : Fin n) :
-- imply
  let mask : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (p i j))
  let A : Tensor ℝ* [n, n] := A
  (A + (mask - 1) * ∞)[i, j] ≈ if p i j then
    A[i, j]
  else
    (-∞ : Tensor ℝ* []) := by
-- proof
  intro mask A'
  conv_lhs =>
    rw [GetAdd.eq.AddGetS A' ((mask - 1) * ∞) i]
  simp only [List.tail_cons]
  conv_lhs =>
    erw [GetAdd.eq.AddGetS (A'[i]) (((mask - 1) * ∞)[i]) j]
  conv_lhs =>
    rw [GetMul.eq.MulGet.scalar (mask - 1) ∞ i]
  conv_lhs =>
    arg 2
    apply GetMul.eq.MulGet.scalar ((mask - 1)[i]) ∞ j
  conv_lhs =>
    rw [GetSub.eq.SubGetS mask (1 : Tensor ℝ* [n, n]) i]
  conv_lhs =>
    arg 2
    arg 1
    arg 1
    arg 2
    apply EqGet1_1 (i := ⟨i, by simp [Length.eq.Get_0.of.GtLength_0]⟩) (s := [n, n]) (α := ℝ*)
  conv_lhs =>
    arg 2
    arg 1
    apply GetSub.eq.SubGetS (mask[i]) (1 : Tensor ℝ* [n]) j
  conv_lhs =>
    arg 2
    arg 1
    arg 2
    apply EqGet1_1 (i := ⟨j, by simp [Length.eq.Get_0.of.GtLength_0]⟩) (s := [n]) (α := ℝ*)
  simp [mask]
  conv_lhs =>
    arg 2
    arg 1
    arg 1
    arg 1
    apply EqGetStack (fun i : Fin n => ([j < n] (↑(p i j).toNat : Tensor ℝ* []))) i
  conv_lhs =>
    arg 2
    arg 1
    arg 1
    apply EqGetStack (fun j : Fin n => (↑(p i j).toNat : Tensor ℝ* [])) j
  split_ifs with h_p
  ·
    simp [h_p]
    apply XEq.of.Eq
    apply Int.EqAdd.of.Eq_Sub.left
    erw [Nat.Sub.eq.Zero]
    apply Tensor.EqMul0_0.of.Eq_0
    apply Int.Sub.eq.Zero.of.Eq
    apply Eq.of.EqDataS
    rw [EqData1'1]
    erw [Eq_TensorReplicate]
    simp
    rfl
  ·
    simp [h_p]
    erw [Nat.cast_zero]
    erw [Sub0.eq.Neg]
    rw [show A' = A.map Hyperreal.ofReal from rfl]
    conv_lhs =>
      arg 1
      arg 1
      apply GetMap.eq.MapGet A Hyperreal.ofReal i
    conv_lhs =>
      arg 1
      apply GetMap.eq.MapGet (A[i]) Hyperreal.ofReal j
    simp [Tensor.map]
    apply XEq.of.XEqDataS
    erw [DataAdd.eq.AddDataS]
    erw [DataMul.eq.MulData]
    simp [DataNeg.eq.NegData]
    conv_lhs =>
      erw [DataNeg.eq.NegData (1 : Tensor ℝ* [])]
    apply XEq.of.All_XEqGetS.fin
    intro k
    erw [@Vector.GetAdd.eq.AddGetS.fin]
    erw [@Vector.GetNeg.eq.NegGet.fin]
    erw [@Vector.GetMul.eq.MulGet.fin]
    erw [@Vector.GetNeg.eq.NegGet.fin]
    erw [Vector.GetMap.eq.UFnGet.fin]
    fin_cases k
    erw [EqData1'1]
    erw [@Vector.EqGet1_1.fin]
    simp only [neg_one_mul]
    erw [Add_Neg.eq.Sub]
    conv_rhs =>
      erw [Vector.Get_0.eq.Head.fin]
    conv_rhs =>
      simp [List.Vector.head]
    apply Sub_Infty.to.NegInfty


-- created on 2025-12-06
-- updated on 2026-08-27
