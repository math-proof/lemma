import Lemma.List.Prod.eq.MulProdS
import Lemma.Nat.Ne_0.of.Mul.ne.Zero
open List Nat


@[main]
private lemma main
  [MonoidWithZero α]
  {s : List α}
-- given
  (h : s.prod ≠ 0) 
  (i : ℕ):
-- imply
  (s.drop i).prod ≠ 0 := by
-- proof
  rw [Prod.eq.MulProdS s i] at h
  apply Ne_0.of.Mul.ne.Zero h


-- created on 2025-09-23
