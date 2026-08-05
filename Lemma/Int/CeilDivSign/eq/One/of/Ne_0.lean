import Lemma.Int.EqSign_1.of.Gt_0
import Lemma.Int.Sign.eq.Neg1.of.Lt_0
import Lemma.Int.GeSign.of.Lt_0
import Lemma.Int.LeSign.of.Gt_0
import Lemma.Int.LtCoeS.is.Lt
import Lemma.Int.LeCoeS.is.Le
import Lemma.Nat.Lt.is.Le.Ne
import Lemma.Nat.NotLt.is.Ge
import Lemma.Rat.EqCeil_1.of.In_Ioc0'1
import Lemma.Rat.Div.gt.Zero.of.Gt_0.Gt_0
import Lemma.Rat.Div.gt.Zero.of.Lt_0.Lt_0
import Lemma.Rat.LeDivS.of.Le.Gt_0
import Lemma.Rat.LeDivS.of.Ge.Lt_0
import Lemma.Rat.Div.eq.One.of.Gt_0
import Lemma.Rat.Div.eq.One.of.Lt_0
import Lemma.Set.In_Ioc.is.Lt.Le
open Set Int Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {d : ℤ}
-- given
  (h : d ≠ 0) :
-- imply
  ⌈sign d / (d : α)⌉ = 1 := by
-- proof
  apply EqCeil_1.of.In_Ioc0'1
  by_cases h₀ : d > 0
  ·
    rw [EqSign_1.of.Gt_0 h₀]
    apply In_Ioc.of.Lt.Le
    ·
      apply Div.gt.Zero.of.Gt_0.Gt_0
      ·
        norm_num
      ·
        simpa using GtCoeS.of.Gt (R := α) h₀
    ·
      have h_one_le_d : (1 : ℤ) ≤ d := by
        have := LeSign.of.Gt_0 h₀
        rw [EqSign_1.of.Gt_0 h₀] at this
        assumption
      have h_d_pos : (d : α) > 0 := by simpa using GtCoeS.of.Gt (R := α) h₀
      rw [← Div.eq.One.of.Gt_0 h_d_pos]
      exact LeDivS.of.Le.Gt_0 (LeCoeS.of.Le (R := α) h_one_le_d) h_d_pos
  ·
    have h_lt : d < 0 := by
      have := Le.of.NotGt h₀
      exact Lt.of.Le.Ne this h
    have h_ge := GeSign.of.Lt_0 h_lt
    rw [Sign.eq.Neg1.of.Lt_0 h_lt] at h_ge
    rw [Sign.eq.Neg1.of.Lt_0 h_lt]
    apply In_Ioc.of.Lt.Le
    ·
      apply Div.gt.Zero.of.Lt_0.Lt_0
      ·
        norm_num
      ·
        simpa using LtCoeS.of.Lt (R := α) h_lt
    ·
      have h_d_neg : (d : α) < 0 := by simpa using LtCoeS.of.Lt (R := α) h_lt
      rw [← Div.eq.One.of.Lt_0 h_d_neg]
      exact LeDivS.of.Ge.Lt_0 (GeCoeS.of.Ge (R := α) h_ge) h_d_neg


-- created on 2023-05-29
