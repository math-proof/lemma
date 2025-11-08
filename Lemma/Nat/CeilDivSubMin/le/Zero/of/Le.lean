import Lemma.Nat.LeCoeS.is.Le
import Lemma.Nat.LeMin.of.Le
import Lemma.Int.Sub.le.Zero.of.Le
import Lemma.Int.GtAdd_1'0
import Lemma.Rat.Div.le.Zero.of.Le_0.Gt_0
import Lemma.Int.LeCeil.is.Le
import Lemma.Nat.Min
open Int Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {start stop : ℕ}
-- given
  (h : stop ≤ start)
  (step n : ℕ) :
-- imply
  ⌈((stop : α) ⊓ (n : α) - start) / (step + 1)⌉ ≤ 0 := by
-- proof
  apply LeCeil.of.Le
  simp
  apply Div.le.Zero.of.Le_0.Gt_0
  .
    apply Sub.le.Zero.of.Le
    apply LeMin.of.Le
    apply LeCoeS.of.Le h
  .
    apply GtAdd_1'0 (R := α) step


@[main]
private lemma left
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {start stop : ℕ}
-- given
  (h : stop ≤ start)
  (step n : ℕ) :
-- imply
  ⌈((n : α) ⊓ (stop : α) - start) / (step + 1)⌉ ≤ 0 := by
-- proof
  rw [Min.comm]
  apply main h


-- created on 2025-05-28
