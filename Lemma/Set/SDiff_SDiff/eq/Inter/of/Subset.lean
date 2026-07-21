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
    simp [Set.mem_sdiff, Set.mem_inter_iff]
    tauto


-- created on 2025-04-08
