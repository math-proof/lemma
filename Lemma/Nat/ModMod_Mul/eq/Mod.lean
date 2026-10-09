import Lemma.Nat.Mul
import sympy.functions.elementary.integers
open Nat


@[path]
private lemma main
  [IntegerRing Z]
-- given
  (k m n : Z) :
-- imply
  k % (m * n) % n = k % n :=
-- proof
  IntegerRing.mod_mul


@[path]
private lemma left
  [IntegerRing Z]
-- given
  (k m n : Z) :
-- imply
  k % (n * m) % n = k % n := by
-- proof
  rw [Mul.comm]
  apply main


-- created on 2025-11-14
-- updated on 2026-08-01
