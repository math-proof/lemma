import sympy.core.power
import Lemma.Basic


@[main]
private lemma main
  [Decidable p] :
-- imply
  Bool.toNat p = (Bool.toNat p) ^ (Nat.succ n) := by
-- proof
  match n with
  | .zero =>
    simp
  | .succ n =>
    by_cases h : p <;>
      simp_all [pow_succ]


-- created on 2025-04-20
