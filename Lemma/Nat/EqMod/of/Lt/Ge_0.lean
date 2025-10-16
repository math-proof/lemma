import sympy.functions.elementary.integers
import Lemma.Nat.Eq_AddMulDiv___Mod
import Lemma.Algebra.Mul.eq.Zero.of.OrAndSEq_0Ge_0
import Lemma.Algebra.Ge.of.Ge.Gt
open Algebra Nat


@[main]
private lemma main
  [IntegerRing Z]
  {k n : Z}
-- given
  (h₀ : k ≥ 0)
  (h₁ : k < n) :
-- imply
  k % n = k := by
-- proof
  have h := Eq_AddMulDiv___Mod (k : Z) n
  apply Eq.symm
  apply h.trans
  suffices k / n * n = 0 by
    rw [this]
    simp
  apply Mul.eq.Zero.of.OrAndSEq_0Ge_0
  left
  constructor
  ·
    apply IntegerRing.div_eq_zero_of_lt
    repeat assumption
  ·
    apply Ge.of.Ge.Gt h₁ h₀


-- created on 2025-08-13
