import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b x t : α}
-- given
  (ht : 0 < t)
  (h : x ∈ Set.Ioc a b) :
-- imply
  x / t ∈ Set.Ioc (a / t) (b / t) := by
-- proof
  obtain ⟨hax, hxb⟩ := h
  exact ⟨div_lt_div_of_pos_right hax ht, div_le_div_of_nonneg_right hxb ht.le⟩


-- created on 2020-06-19
-- updated on 2023-04-17
