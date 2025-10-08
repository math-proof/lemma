import Lemma.Algebra.LeCoeS.is.Le
import Lemma.Algebra.LeMin.of.Le
import Lemma.Algebra.Sub.le.Zero.of.Le
import Lemma.Int.GtAdd_1'0
import Lemma.Algebra.Div.le.Zero.of.Le_0.Gt_0
import Lemma.Algebra.LeCeil.is.Le
import Lemma.Algebra.Min
open Algebra Int


@[main]
private lemma main
  {start stop : ℕ}
-- given
  (h : stop ≤ start)
  (step n : ℕ) :
-- imply
  ⌈((stop : ℚ) ⊓ (n : ℚ) - start) / (step + 1)⌉ ≤ 0 := by
-- proof
  have h := LeCoeS.of.Le.nat (R := ℚ) h
  have h := LeMin.of.Le h (n : ℚ)
  have h := Sub.le.Zero.of.Le h
  have h_gt_0 := GtAdd_1'0 (R := ℚ) step
  have h := Div.le.Zero.of.Le_0.Gt_0 h h_gt_0
  apply LeCeil.of.Le h


@[main]
private lemma left
  {start stop : ℕ}
-- given
  (h : stop ≤ start)
  (step n : ℕ) :
-- imply
  ⌈((n : ℚ) ⊓ (stop : ℚ) - start) / (step + 1)⌉ ≤ 0 := by
-- proof
  rw [Min.comm]
  apply main h


-- created on 2025-05-28
