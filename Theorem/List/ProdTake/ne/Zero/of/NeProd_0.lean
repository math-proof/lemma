module
public import Theorem.Nat.Ne_0.of.Mul.ne.Zero
public import Theorem.List.Prod.eq.MulProdS
open List Nat


public section

@[path]
private theorem main
  [MonoidWithZero α]
  {s : List α}
-- given
  (h : s.prod ≠ 0)
  (i : ℕ):
-- imply
  (s.take i).prod ≠ 0 := by
-- proof
  rw [Prod.eq.MulProdS s i] at h
  apply Ne_0.of.Mul.ne.Zero.left h


-- created on 2025-09-23
