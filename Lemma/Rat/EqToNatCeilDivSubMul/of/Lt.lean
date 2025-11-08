import Lemma.Rat.EqCeilDivSubMul.of.Lt
open Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {m n j : ℕ}
-- given
  (h : j < n) :
-- imply
  ⌈(m * n - j : α) / n⌉.toNat = m := by
-- proof
  simp [EqCeilDivSubMul.of.Lt h]


-- created on 2025-11-08
