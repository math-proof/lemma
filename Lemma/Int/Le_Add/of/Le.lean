import Lemma.Nat.Le.of.Le.Le
open Nat


@[path]
private lemma left
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h : x ≤ y)
  (n : ℕ) :
-- imply
  x ≤ n + y := by
-- proof
  apply Le.of.Le.Le h (by simp)


@[path]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h : x ≤ y)
  (n : ℕ) :
-- imply
  x ≤ y + n := by
-- proof
  apply Le.of.Le.Le h (by simp)


-- created on 2025-10-16
