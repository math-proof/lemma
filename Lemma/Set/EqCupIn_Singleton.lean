import sympy.Basic


@[main]
private lemma main
-- given
  (g : α → Set α)
  (a : α) :
-- imply
  ⋃ x ∈ ({a} : Set α), g x = g a :=
-- proof
  Set.biUnion_singleton a g

-- created on 2025-07-20
