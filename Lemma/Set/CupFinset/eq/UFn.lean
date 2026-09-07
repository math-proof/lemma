import sympy.Basic


@[main]
private lemma main
-- given
  (f : α → Set β):
-- imply
  ⋃ x ∈ ({a} : Set α), f x = f a := by
-- proof
  simp


-- created on 2025-08-14
