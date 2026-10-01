import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
  [Decidable p]
  [Decidable q]
  {a b : α} :
-- imply
  (if p ∨ q then a else b) = if p then a else if ¬q then b else a := by
-- proof
  by_cases hp : p
  · simp [hp]
  · by_cases hq : q
    · simp [hp, hq]
    · simp [hp, hq]


-- created on 2022-01-03
