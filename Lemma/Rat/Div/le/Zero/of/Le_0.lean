import Lemma.Rat.Div.le.Zero.of.Ge_0.Le_0
import Lemma.Rat.Div.le.Zero.of.Le_0.Ge_0
open Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α}
-- given
  (h : x ≤ 0)
  (d : ℕ) :
-- imply
  x / d ≤ 0 := by
-- proof
  apply Div.le.Zero.of.Le_0.Ge_0 h
  simp


@[main]
private lemma left
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α}
-- given
  (h : x ≤ 0)
  (d : ℕ) :
-- imply
  d / x ≤ 0 := by
-- proof
  apply Div.le.Zero.of.Ge_0.Le_0 _ h
  simp


-- created on 2025-11-07
