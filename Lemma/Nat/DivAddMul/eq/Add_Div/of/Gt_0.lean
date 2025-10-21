import Lemma.Nat.Mul
open Nat


@[main]
private lemma left
-- given
  (h : c > 0)
  (a b : ℕ) :
-- imply
  (c * a + b) / c = a + b / c :=
-- proof
  Nat.mul_add_div h a b


@[main]
private lemma main
-- given
  (h : c > 0)
  (a b : ℕ) :
-- imply
  (a * c + b) / c = a + b / c := by
-- proof
  rw [Mul.comm]
  apply left h


-- created on 2025-10-21
