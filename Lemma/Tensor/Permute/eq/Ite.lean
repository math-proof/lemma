import sympy.tensor.tensor
import Lemma.List.EqPermute__0
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.Gt_0.EqVal_0
import Lemma.List.ProdPermute.eq.MulProd_ProdAppend.of.Gt_0
import Lemma.List.Permute.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1.Le_0
import Lemma.Algebra.NotGt.is.Le
import Lemma.List.ProdPermute.eq.MulProd_ProdDrop.of.Val.ne.SubLength_1.Le_0
import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.Int.NegSucc.eq.NegCoeAdd_1
import Lemma.Nat.Add
import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.Int.ToNatSubOfNat_NegSucc.eq.AddAdd1
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.SubMin.eq.MinSubS
import Lemma.Nat.Min.eq.Add_1
open Algebra List Bool Int Nat


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (i : Fin s.length)
  (d : ℤ) :
-- imply
  X.permute i d =
    if h_k : d = 0 then
      cast (by simp_all [EqPermute__0]) X
    else if h_k : d > 0 then
      if h_d : i.val = 0 then
        cast (by rw [Permute.eq.AppendRotateTake___Drop.of.Gt_0.EqVal_0 h_d h_k]) (X.permuteHead (d + 1).toNat)
      else
        ⟨cast (by rw [ProdPermute.eq.MulProd_ProdAppend.of.Gt_0 h_k i]) ((X.data.splitAt i).map fun data => ((⟨data⟩ : Tensor α (s.drop i)).permuteHead (d + 1).toNat).data).flatten⟩
    else
      have h_k := Le.of.NotGt h_k
      if h_d : i.val = s.length - 1 then
        cast (by rw [Permute.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1.Le_0 h_k h_d]) ((X.permuteTail (1 - d).toNat))
      else
        ⟨cast (by rw [ProdPermute.eq.MulProd_ProdDrop.of.Val.ne.SubLength_1.Le_0 h_k h_d]) ((⟨X.data.splitAt (i + 1)⟩ : Tensor (List.Vector α (s.drop (i + 1)).prod) (s.take (i + 1))).permuteTail (1 - d).toNat).data.flatten⟩ := by
-- proof
  unfold Tensor.permute
  match d with
  | Int.ofNat offset =>
    match offset with
    | 0 =>
      simp
    | Nat.succ offset =>
      simp
      split_ifs with h_d? h_offset h_offset
      ·
        linarith
      ·
        congr
      ·
        linarith
      ·
        congr
  | Int.negSucc offset =>
    simp
    split_ifs with h_d
    ·
      apply EqCastS.of.SEq.Eq.left
      ·
        rw [NegSucc.eq.NegCoeAdd_1]
        rwa [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1]
      ·
        rw [ToNatSubOfNat_NegSucc.eq.AddAdd1]
        simp
        rw [Add.comm]
    ·
      simp
      apply EqCastS.of.SEq.Eq.left (n := (s.permute i (-↑(offset + 1))).prod)
      ·
        rw [Permute__Neg.eq.Append_AppendRotateTakeDrop]
        simp
        rw [Mul_Mul.eq.MulMul]
        apply EqMulS.of.Eq
        have h : (i.val + 1) ⊓ s.length - (offset + 2) = i - (offset + 1) := by
          rw [Min.eq.Add_1]
          simp
        rw [h]
        apply EqMulS.of.Eq.left
        rw [Min.eq.Add_1]
        rw [SubMin.eq.MinSubS]
        simp
      ·
        rw [ToNatSubOfNat_NegSucc.eq.AddAdd1]
        simp
        rw [Add.comm (a := 2)]


-- created on 2025-07-14
-- updated on 2025-07-18
