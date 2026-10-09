import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {c : Prop}
  [Decidable c]
  {a b : ℤ} :
-- imply
  ({if c then a else b} : Set ℤ) = if c then {a} else {b} := by
-- proof
  split_ifs <;> rfl


-- created on 2023-11-12
