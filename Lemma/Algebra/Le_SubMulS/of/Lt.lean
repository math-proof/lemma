import Lemma.Algebra.AddMul.le.Mul
import Lemma.Algebra.Le_Sub.of.LeAdd
import Lemma.Nat.Add
import Lemma.Nat.Mul
import Lemma.Algebra.AddMul.le.Mul.of.Lt
open Algebra Nat


@[main]
private lemma left
  {n : ℕ}
-- given
  (h : i < n)
  (m : ℕ) :
-- imply
  m ≤ m * n - m * i := by
-- proof
  have h := AddMul.le.Mul.of.Lt h m
  apply Le_Sub.of.LeAdd.nat
  rwa [Add.comm]


@[main]
private lemma main
  {n : ℕ}
-- given
  (h : i < n)
  (m : ℕ) :
-- imply
  m ≤ n * m - i * m := by
-- proof
  rw [Mul.comm]
  rw [Mul.comm (a := i)]
  apply left h


-- created on 2025-05-31
