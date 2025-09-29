import sympy.Basic


@[main]
private lemma main
  {a b : α} :
-- imply
  a ∈ ({a, b} : Set α) :=
-- proof
  Set.mem_insert a ({b} : Set α)


-- created on 2025-04-04
