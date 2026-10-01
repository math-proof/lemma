import sympy.Basic


@[main]
private lemma contraposition :
-- imply
  (p ↔ q) ↔ (¬q ↔ ¬p) := by
-- proof
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]


-- created on 2022-01-27
