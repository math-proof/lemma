import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
  [Decidable p] [Decidable q]
  {x y z : α} :
-- imply
  (if p then x else if q then y else z) ∈ ({x, y, z} : Set α) := by
-- proof
  split_ifs <;> simp


-- created on 2018-11-16
-- updated on 2026-08-20
