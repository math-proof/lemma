import sympy.Basic


@[main]
private lemma Comm
  {a b : Set α} :
-- imply
  a ∪ b = b ∪ a := by
-- proof
  rw [Set.union_comm]


-- created on 2025-06-06
