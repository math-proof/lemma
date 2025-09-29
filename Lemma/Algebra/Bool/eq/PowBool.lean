import sympy.core.power
import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  [NeZero n] :
-- imply
  Bool.toNat p = (Bool.toNat p) ^ n := by
-- proof
  match h : n with
  | .zero =>
    have h := NeZero.ne n
    contradiction
  | .succ n =>
    by_cases h : p <;>
      simp_all [pow_succ]


-- created on 2025-04-20
