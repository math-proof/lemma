import Lemma.Hyperreal.InfiniteNeg.is.XEqExp_0
import Lemma.Hyperreal.InfinitePos.is.InfiniteNegSub
import Lemma.Hyperreal.InfinitePosInfty
import Lemma.Hyperreal.XEq.of.Eq
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataSub.eq.SubDataS
import Lemma.Tensor.EqGet1_1
import Lemma.Tensor.EqHeadData
import Lemma.Tensor.GetExp.eq.ExpGet
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.GetMul.eq.MulGet
import Lemma.Tensor.GetSub.eq.SubGetS
import Lemma.Tensor.XEq.is.All_XEqGetS.of.GtLength_0
import Lemma.Vector.GetExp.eq.ExpGet
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetSub.eq.SubGetS
open Hyperreal Tensor
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
  apply XEq.of.All_XEqGetS.GtLength_0 (h := by simp)
  intro i
  apply XEq.of.All_XEqGetS.GtLength_0 (h := by simp)
  intro j
  simp
  have := GetExp.eq.ExpGet.fin (A' + (Ξ - 1) * ∞) ⟨i, by grind⟩
  simp at this
  rw [this]
  have := GetExp.eq.ExpGet.fin ((A' + (Ξ - 1) * ∞).get i) ⟨j, by grind⟩
  simp at this
  erw [this]
  simp [Ξ]
  apply XEq.of.XEqDataS
  erw [DataExp.eq.ExpData]
  rw [GetAdd.eq.AddGetS.fin]
  erw [GetAdd.eq.AddGetS.fin]
  have hi : ↑i < n := i.isLt
  have hj : ↑j < n := j.isLt
  erw [congrArg Tensor.data
    (congrArg (fun X => X.get ⟨↑j, hj⟩)
      (GetMul.eq.MulGetS.fin
        (Exp.exp A')
        ([i < n] [j < n] ↑(p i j).toNat)
        ⟨↑i, hi⟩))]
  erw [congrArg Tensor.data
    (GetMul.eq.MulGetS.fin
      ((Exp.exp A').get ⟨↑i, hi⟩)
      (([i < n] [j < n] ↑(p i j).toNat).get ⟨↑i, hi⟩)
      ⟨↑j, hj⟩)]
  let mask : Tensor ℝ* [n, n] := [i < n] [j < n] ((p i j).toNat : Tensor ℝ* [])
  refine
    (congrArg
      (fun t => Exp.exp ((A'.get i).get ⟨↑j, hj⟩ + t).data)
      ((congrArg (fun X : Tensor ℝ* [n] => X.get ⟨↑j, hj⟩)
          (by
            convert GetMul.eq.MulGet.scalar.fin (mask - 1) ω ⟨↑i, hi⟩ <;> rfl)).trans
        (GetMul.eq.MulGet.scalar.fin ((mask - 1).get ⟨↑i, hi⟩) ω ⟨↑j, hj⟩))) ▸ ?_
  have hE₁ := GetExp.eq.ExpGet.fin A' ⟨↑i, hi⟩
  simp at hE₁
  have hE₂ := GetExp.eq.ExpGet.fin (A'.get ⟨↑i, hi⟩) ⟨↑j, hj⟩
  simp at hE₂
  refine
    (congrArg Tensor.data
      (congrArg
        (fun x : Tensor ℝ* [] =>
          x * (([i < n] [j < n] ↑(p i j).toNat).get ⟨↑i, hi⟩).get ⟨↑j, hj⟩)
        (hE₁.symm ▸ hE₂))).symm ▸ ?_
  have hmsk :
      (mask.get ⟨↑i, hi⟩).get ⟨↑j, hj⟩ = ((p i j).toNat : Tensor ℝ* []) := by
    apply Eq.trans (b := ([j < n] ((p ⟨↑i, hi⟩ j).toNat : Tensor ℝ* [])).get ⟨↑j, hj⟩)
    ·
      apply congrArg (fun X : Tensor ℝ* [n] => X.get ⟨↑j, hj⟩)
      apply EqGetStack.fin (fun i : Fin n => [j < n] ((p i j).toNat : Tensor ℝ* [])) ⟨↑i, hi⟩
    apply Eq.trans
    ·
      apply EqGetStack.fin (fun j : Fin n => ((p ⟨↑i, hi⟩ j).toNat : Tensor ℝ* [])) ⟨↑j, hj⟩
    congr 1
  apply @Vector.XEq.of.All_XEqGetS.fin
  intro k
  fin_cases k
  rw [Vector.GetExp.eq.ExpGet.fin]
  erw [DataAdd.eq.AddDataS]
  erw [Vector.GetAdd.eq.AddGetS.fin]
  erw [DataMul.eq.MulData]
  erw [Vector.GetMul.eq.MulGet.fin]
  erw [DataMul.eq.MulDataS]
  erw [Vector.GetMul.eq.MulGetS.fin]
  erw [DataExp.eq.ExpData]
  erw [Vector.GetExp.eq.ExpGet.fin]
  have hA :
      ((A'.get i).get ⟨↑j, hj⟩).data.get ⟨0, Nat.zero_lt_one⟩ =
        ((A'.get ⟨↑i, hi⟩).get ⟨↑j, hj⟩).data.get ⟨0, Nat.zero_lt_one⟩ := by
    apply congrArg (fun t : Tensor ℝ* [] => t.data.get ⟨0, Nat.zero_lt_one⟩)
    congr 1
  refine
    (congrArg₂ (fun a b => Exp.exp (a + b * ω)) hA
      (congrArg (fun t : Tensor ℝ* [] => t.data.get ⟨0, Nat.zero_lt_one⟩)
        (((congrArg (fun X : Tensor ℝ* [n] => X.get ⟨↑j, hj⟩)
            ((GetSub.eq.SubGetS.fin mask (1 : Tensor ℝ* [n, n]) ⟨↑i, hi⟩).trans
              (congrArg (fun t => mask.get ⟨↑i, hi⟩ - t)
                (EqGet1_1.fin (i := ⟨↑i, hi⟩) (s := [n, n]) (α := ℝ*))))).trans
          ((GetSub.eq.SubGetS.fin (mask.get ⟨↑i, hi⟩) (1 : Tensor ℝ* [n]) ⟨↑j, hj⟩).trans
            (congrArg (fun t => (mask.get ⟨↑i, hi⟩).get ⟨↑j, hj⟩ - t)
              (EqGet1_1.fin (i := ⟨↑j, hj⟩) (s := [n]) (α := ℝ*))))).trans
          (congrArg (fun t : Tensor ℝ* [] => Sub.sub t (1 : Tensor ℝ* [])) hmsk)))) ▸ ?_
  refine
    (congrArg₂ (fun a b => Exp.exp a * b) hA
      (congrArg (fun t : Tensor ℝ* [] => t.data.get ⟨0, Nat.zero_lt_one⟩) hmsk)).symm ▸ ?_
  erw [DataSub.eq.SubDataS]
  erw [Vector.GetSub.eq.SubGetS.fin]
  erw [EqData1'1]
  erw [Vector.EqGet1_1.fin]
  if h : p i j then
    have hcast :
        (↑(p i j).toNat : Tensor ℝ* []).data.get ⟨0, Nat.zero_lt_one⟩ = ((1 : ℕ) : ℝ*) :=
      (congrArg (fun n : ℕ => (n : Tensor ℝ* []).data.get ⟨0, Nat.zero_lt_one⟩)
        (by simp [h])).trans
        ((Vector.Get_0.eq.Head.fin ((1 : ℕ) : Tensor ℝ* []).data).trans (EqHeadData.nat (1 : ℕ)))
    refine
      (congrArg
        (fun t : ℝ* =>
          Exp.exp
            (((A'.get ⟨↑i, hi⟩).get ⟨↑j, hj⟩).data.get ⟨0, Nat.zero_lt_one⟩ +
              (t - 1) * ω))
        hcast) ▸ ?_
    refine
      (congrArg
        (fun t : ℝ* =>
          Exp.exp (((A'.get ⟨↑i, hi⟩).get ⟨↑j, hj⟩).data.get ⟨0, Nat.zero_lt_one⟩) * t)
        hcast) ▸ ?_
    apply XEq.of.Eq
    simp
  else
    have hcast :
        (↑(p i j).toNat : Tensor ℝ* []).data.get ⟨0, Nat.zero_lt_one⟩ = ((0 : ℕ) : ℝ*) :=
      (congrArg (fun n : ℕ => (n : Tensor ℝ* []).data.get ⟨0, Nat.zero_lt_one⟩)
        (by simp [h])).trans
        ((Vector.Get_0.eq.Head.fin ((0 : ℕ) : Tensor ℝ* []).data).trans (EqHeadData.nat (0 : ℕ)))
    refine (congrArg (fun t : ℝ* => Exp.exp (((A'.get ⟨↑i, hi⟩).get ⟨↑j, hj⟩).data.get ⟨0, Nat.zero_lt_one⟩ + (t - 1) * ω)) hcast) ▸ ?_
    refine (congrArg (fun t : ℝ* => Exp.exp (((A'.get ⟨↑i, hi⟩).get ⟨↑j, hj⟩).data.get ⟨0, Nat.zero_lt_one⟩) * t) hcast) ▸ ?_
    simp
    rw [Int.Add_Neg.eq.Sub]
    apply XEqExp_0.of.InfiniteNeg
    refine
      (congrArg (fun t => t - ω)
        (((congrArg (fun t : Tensor ℝ* [n] => (t.get ⟨↑j, hj⟩).data.get ⟨0, Nat.zero_lt_one⟩)
            ((by rfl : A' = map Hyperreal.ofReal A) ▸
              GetMap.eq.MapGet.fin A Hyperreal.ofReal ⟨↑i, hi⟩)).trans
          (congrArg (fun t : Tensor ℝ* [] => t.data.get ⟨0, Nat.zero_lt_one⟩)
            (GetMap.eq.MapGet.fin (A.get ⟨↑i, hi⟩) Hyperreal.ofReal ⟨↑j, hj⟩))).trans
          (Vector.GetMap.eq.UFnGet
            ((A.get ⟨↑i, hi⟩).get ⟨↑j, hj⟩).data
            Hyperreal.ofReal
            ⟨0, Nat.zero_lt_one⟩))) ▸ ?_
    apply InfiniteNegSub.of.InfinitePos _ InfinitePosInfty


-- created on 2023-06-18
-- updated on 2026-08-28
