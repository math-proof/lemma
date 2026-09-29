import sympy.Basic


@[main]
private lemma main
  [Decidable p] :
-- imply
  Bool.toNat p = 1 ↔ p := by
-- proof
  by_cases hp : p <;> simp [hp]


-- created on 2026-09-27
