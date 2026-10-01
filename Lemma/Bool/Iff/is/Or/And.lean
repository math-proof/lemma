import sympy.Basic


@[main]
private lemma main :
-- imply
  (p ↔ q) ↔ ¬p ∧ ¬q ∨ p ∧ q := by
-- proof
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]


-- created on 2022-01-27
