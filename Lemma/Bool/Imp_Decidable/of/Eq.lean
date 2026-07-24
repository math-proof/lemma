import sympy.Basic


@[main]
private lemma main
  {f g : α → Prop}
-- given
  (h : f = g) :
-- imply
  ((x : α) → Decidable (f x)) = ((x : α) → Decidable (g x)) := by
-- proof
  rw [h]


-- created on 2025-07-16
