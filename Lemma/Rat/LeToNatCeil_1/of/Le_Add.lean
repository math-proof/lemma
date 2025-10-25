import Lemma.Algebra.Div.eq.One.of.Gt_0
import Lemma.Bool.Ne.is.NotEq
import Lemma.Nat.Gt_0.of.Ne_0
import Lemma.Nat.LeSub.is.Le_Add
import Lemma.Nat.LeCoeS.is.Le
import Lemma.Rat.LeDivS.of.Le.Gt_0
import Lemma.Rat.LeCeil.is.Le
import Lemma.Int.LeToNat.is.Le
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Nat.NotGe.is.Lt
import Lemma.Nat.LtCoeS.is.Lt
import Lemma.Algebra.Sub.lt.Zero.of.Lt
import Lemma.Rat.Div.lt.Zero.of.Lt_0.Gt_0
import Lemma.Nat.Le.of.Lt
import Lemma.Int.EqToNat_0.of.Le_0
open Algebra Bool Int Nat Rat


@[main]
private lemma main
  {start stop step : ℕ}
-- given
  (h : stop ≤ start + step) :
-- imply
  ⌈(stop - start : ℚ) / step⌉.toNat ≤ 1 := by
-- proof
  by_cases h_step : step = 0
  ·
    simp [h_step]
  ·
    have h_step := Ne.of.NotEq h_step
    have h_step := Gt_0.of.Ne_0 h_step
    have h_Gt_0 : (step : ℚ) > 0 := by simp_all
    by_cases h_Ge : stop ≥ start
    ·
      have h := LeSub.of.Le_Add.left h
      have h := LeCoeS.of.Le (R := ℚ) h
      have h := LeDivS.of.Le.Gt_0 h h_Gt_0
      simp [Div.eq.One.of.Gt_0 h_Gt_0] at h
      have h := LeCeil.of.Le h
      have h := LeToNat.of.Le h
      rwa [SubCoeS.eq.CoeSub.of.Ge h_Ge]
    ·
      have h := Lt.of.NotGe h_Ge
      have h := LtCoeS.of.Lt (R := ℚ) h
      have h := Sub.lt.Zero.of.Lt h
      have h := Div.lt.Zero.of.Lt_0.Gt_0 h h_Gt_0
      have h := Le.of.Lt h
      have h := LeCeil.of.Le h
      have h := EqToNat_0.of.Le_0 h
      simp [h]


-- created on 2025-05-24
