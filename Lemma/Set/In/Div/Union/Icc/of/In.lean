import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b c d e x : α}
-- given
  (he : 0 < e)
  (h : x ∈ Set.Ico a b ∪ Set.Ico c d) :
-- imply
  x / e ∈ Set.Ico (a / e) (b / e) ∪ Set.Ico (c / e) (d / e) := by
-- proof
  simp only [Set.mem_union] at h
  obtain h | h := h
  · obtain ⟨hax, hxb⟩ := h
    exact Or.inl ⟨div_le_div_of_nonneg_right hax he.le, div_lt_div_of_pos_right hxb he⟩
  · obtain ⟨hcx, hxd⟩ := h
    exact Or.inr ⟨div_le_div_of_nonneg_right hcx he.le, div_lt_div_of_pos_right hxd he⟩


-- created on 2021-03-04
