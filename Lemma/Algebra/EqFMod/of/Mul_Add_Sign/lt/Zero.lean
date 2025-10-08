import Lemma.Algebra.EqSign_1.of.Gt_0
import Lemma.Algebra.NotGt.is.Le
import Lemma.Algebra.Lt.of.Le.Ne
import Lemma.Bool.Ne.is.NotEq
import Lemma.Algebra.Sign.eq.Neg1.of.Lt_0
import Lemma.Algebra.AddSub.eq.Sub_Sub
import Lemma.Algebra.GeSub_1.of.Gt
import Lemma.Set.In_Icc.of.MulSubS.le.Zero.Le
import Lemma.Algebra.Sub.eq.Add_Neg
import Lemma.Algebra.Sub_Add.eq.SubSub
import Lemma.Algebra.LeAdd_1.of.Lt
import Lemma.Nat.Mul
import Lemma.Set.EqFMod.of.Gt_Zero.Icc0Sub_1
import Lemma.Set.EqFMod.of.Lt_0.IccAdd_1'0
open Algebra Set Bool Nat


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : n * (n - d + sign d) ≤ 0) :
-- imply
  n.fmod d = n := by
-- proof
  -- Consider the cases for the sign of d
  by_cases h_d : d = 0
  ·
    rw [h_d]
    norm_num
  ·
    by_cases h_d' : d > 0
    ·
      have := EqSign_1.of.Gt_0 h_d'
      rw [this] at h
      rw [AddSub.eq.Sub_Sub] at h
      have := GeSub_1.of.Gt h_d'
      have h_Mem : n ∈ Icc 0 (d - 1) := by
        apply In_Icc.of.MulSubS.le.Zero.Le _ this
        norm_num
        exact h
      apply EqFMod.of.Gt_Zero.Icc0Sub_1 h_d' h_Mem
    ·
      have := Le.of.NotGt h_d'
      have h_d := Ne.of.NotEq h_d
      have h_d := Lt.of.Le.Ne h_d this
      have := Sign.eq.Neg1.of.Lt_0 h_d
      rw [this] at h
      rw [Add_Neg.eq.Sub] at h
      rw [SubSub.eq.Sub_Add] at h
      have := LeAdd_1.of.Lt h_d
      rw [Mul.comm] at h
      have h_Mem : n ∈ Icc (d + 1) 0 := by
        apply In_Icc.of.MulSubS.le.Zero.Le _ this
        norm_num
        exact h
      apply EqFMod.of.Lt_0.IccAdd_1'0 h_d h_Mem


-- created on 2025-03-29
-- updated on 2025-03-30
