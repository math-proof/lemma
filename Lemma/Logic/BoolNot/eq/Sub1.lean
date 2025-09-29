import sympy.Basic


@[main]
private lemma main
  [Decidable p] :
-- imply
  Bool.toNat (¬p) = 1 - Bool.toNat p := by
-- proof
  by_cases h : p <;>
  ·
    simp_all


-- created on 2025-07-20
