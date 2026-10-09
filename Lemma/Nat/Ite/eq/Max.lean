import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {p q : Prop}
  [Decidable p]
  [Decidable q]
  {s : EReal} :
-- imply
  (if p ∨ q then s else ⊥) = max (if p then s else ⊥) (if q then s else ⊥) := by
-- proof
  by_cases hp : p
  · by_cases hq : q
    · simp [hp, hq]
    · simp [hp, hq]
  · by_cases hq : q
    · simp [hp, hq]
    · simp [hp, hq]


-- created on 2023-04-23
