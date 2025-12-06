import sympy.core.power
import sympy.Basic


@[main, comm]
private lemma main
  [Decidable p] :
-- imply
  Bool.toNat p = (Bool.toNat p)² := by
-- proof
  by_cases h : p <;>
    simp [h]


-- created on 2025-04-20
