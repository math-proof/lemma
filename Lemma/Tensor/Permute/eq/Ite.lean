import sympy.tensor.tensor
import Lemma.List.EqPermute__0
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.Gt_0.EqVal_0
import Lemma.List.ProdPermute.eq.MulProd_ProdAppend.of.Gt_0
import Lemma.List.Permute.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1.Le_0
import Lemma.Algebra.NotGt.is.Le
import Lemma.List.ProdPermute.eq.MulProd_ProdDrop.of.Val.ne.SubLength_1.Le_0
import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.Algebra.NegSucc.eq.NegCoeAdd_1
import Lemma.Algebra.Add
import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.Algebra.ToNatSubOfNat_NegSucc.eq.AddAdd1
import Lemma.Algebra.EqMulS.of.Eq
import Lemma.Algebra.MulMul.eq.Mul_Mul
import Lemma.Algebra.SubMin.eq.MinSubS
import Lemma.Algebra.Min.eq.Add_1
open Algebra List Bool


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (k : ℤ) :
-- imply
  X.permute d k =
    if h_k : k = 0 then
      cast (by simp_all [EqPermute__0]) X
    else if h_k : k > 0 then
      if h_d : d.val = 0 then
        cast (by rw [Permute.eq.AppendRotateTake___Drop.of.Gt_0.EqVal_0 h_d h_k]) (X.permuteHead (k + 1).toNat)
      else
        ⟨cast (by rw [ProdPermute.eq.MulProd_ProdAppend.of.Gt_0 h_k d]) ((X.data.splitAt d).map fun data => ((⟨data⟩ : Tensor α (s.drop d)).permuteHead (k + 1).toNat).data).flatten⟩
    else
      have h_k := Le.of.NotGt h_k
      if h_d : d.val = s.length - 1 then
        cast (by rw [Permute.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1.Le_0 h_k h_d]) ((X.permuteTail (1 - k).toNat))
      else
        ⟨cast (by rw [ProdPermute.eq.MulProd_ProdDrop.of.Val.ne.SubLength_1.Le_0 h_k h_d]) ((⟨X.data.splitAt (d + 1)⟩ : Tensor (List.Vector α (s.drop (d + 1)).prod) (s.take (d + 1))).permuteTail (1 - k).toNat).data.flatten⟩ := by
-- proof
  unfold Tensor.permute
  match k with
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
      apply EqCastS.of.SEq.Eq.left (n := (s.permute d (-↑(offset + 1))).prod)
      ·
        rw [Permute__Neg.eq.Append_AppendRotateTakeDrop]
        simp
        rw [Mul_Mul.eq.MulMul]
        apply EqMulS.of.Eq
        have h : (d.val + 1) ⊓ s.length - (offset + 2) = d - (offset + 1) := by
          rw [Min.eq.Add_1]
          simp
        rw [h]
        apply EqMulS.of.Eq.left
        rw [Min.eq.Add_1]
        rw [SubMin.eq.MinSubS.nat]
        simp
      ·
        rw [ToNatSubOfNat_NegSucc.eq.AddAdd1]
        simp
        rw [Add.comm (a := 2)]


-- created on 2025-07-14
-- updated on 2025-07-18
