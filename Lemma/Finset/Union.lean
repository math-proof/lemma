import sympy.Basic


@[main]
private lemma Comm
  [DecidableEq ι]
  {a b : Finset ι} :
-- imply
  a ∪ b = b ∪ a := by
-- proof
  rw [Finset.union_comm]


-- created on 2025-12-30
