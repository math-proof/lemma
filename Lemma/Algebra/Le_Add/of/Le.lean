import Lemma.Algebra.Le.of.Le.Le
open Algebra


@[main]
private lemma nat
  {x y : ℕ}
-- given
  (h : x ≤ y)
  (n : ℕ):
-- imply
  x ≤ n + y := by
-- proof
  apply Le.of.Le.Le h (by simp)


@[main]
private lemma left
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h : x ≤ y)
  (n : ℕ):
-- imply
  x ≤ n + y := by
-- proof
  apply Le.of.Le.Le h (by simp)


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h : x ≤ y)
  (n : ℕ):
-- imply
  x ≤ y + n := by
-- proof
  apply Le.of.Le.Le h (by simp)


-- created on 2025-05-04
