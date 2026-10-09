import sympy.Basic


@[path]
private lemma main
  {A B : Set α}
-- given
  (h : A \ B = A) :
-- imply
  A ∩ B = ∅ := by
-- proof
  rw [← h]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hx ↦ hx.2


-- created on 2021-04-04
