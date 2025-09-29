import sympy.Basic


@[main]
private lemma main
  {A B: Set α}
-- given
  (h : A ⊆ B)
  (C : Set α) :
-- imply
  A \ (B \ C) = A ∩ C := by
-- proof
  ext x
  constructor <;>
  ·
    simp [Set.mem_diff, Set.mem_inter_iff]
    -- For each direction, we use the fact that A is a subset of B to simplify the set membership conditions.
    tauto


-- created on 2025-04-08
