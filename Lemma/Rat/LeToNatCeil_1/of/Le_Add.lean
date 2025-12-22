import Lemma.Nat.OfNat.eq.Cast
import Lemma.Rat.Div.eq.One.of.Gt_0
import Lemma.Bool.Ne.is.NotEq
import Lemma.Nat.Gt_0.of.Ne_0
import Lemma.Nat.LeSub.is.Le_Add
import Lemma.Nat.LeCoeS.is.Le
import Lemma.Rat.LeDivS.of.Le.Gt_0
import Lemma.Nat.LeCeil.is.Le
import Lemma.Int.LeToNat.is.Le
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Nat.NotGe.is.Lt
import Lemma.Nat.LtCoeS.is.Lt
import Lemma.Int.Lt.is.Gt0Sub
import Lemma.Rat.Gt0Div.of.Lt_0.Gt_0
import Lemma.Nat.Le.of.Lt
import Lemma.Int.EqToNat_0.of.Le_0
open Bool Int Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {start stop step : ℕ}
-- given
  (h : stop ≤ start + step) :
-- imply
  ⌈(stop - start : α) / step⌉.toNat ≤ 1 := by
-- proof
  if h_step : step = 0 then
    simp [h_step]
  else
    have h_step := Ne.of.NotEq h_step
    have h_step := Gt_0.of.Ne_0 h_step
    have h_pos : (step : α) > 0 := by simp_all
    if h_ge : stop ≥ start then
      have h := LeSub.of.Le_Add.left h
      have h := LeCoeS.of.Le (R := α) h
      have h := LeDivS.of.Le.Gt_0 h h_pos
      simp [Div.eq.One.of.Gt_0 h_pos] at h
      rw [OfNat.eq.Cast] at h
      have h := LeCeil.of.Le h
      have h := LeToNat.of.Le h
      rwa [SubCoeS.eq.CoeSub.of.Ge h_ge]
    else
      have h := Lt.of.NotGe h_ge
      have h := LtCoeS.of.Lt (R := α) h
      have h := Gt0Sub.of.Lt h
      have h := Gt0Div.of.Lt_0.Gt_0 h h_pos
      have h := Le.of.Lt h
      rw [OfNat.eq.Cast] at h
      have h := LeCeil.of.Le h
      have h := EqToNat_0.of.Le_0 h
      simp [h]


-- created on 2025-05-24
