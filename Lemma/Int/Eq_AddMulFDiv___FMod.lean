import sympy.functions.elementary.integers
import Lemma.Nat.Mul
open Nat


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  n = n // d * d + n.fmod d := by
-- proof
  apply Eq.symm
  rw [Mul.comm]
  apply Int.mul_fdiv_add_fmod n d


-- created on 2025-03-21
