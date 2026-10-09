import sympy.Basic


@[path]
private lemma principle.inclusive_exclusive
  [Decidable p] [Decidable q] :
-- imply
  (decide p).toNat + (decide q).toNat = (decide (p ∨ q)).toNat + (decide (p ∧ q)).toNat := by
-- proof
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]


-- created on 2026-09-27
