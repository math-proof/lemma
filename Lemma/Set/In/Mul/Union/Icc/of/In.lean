import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b c d e : ℝ}
-- given
  (he : 0 < e)
  (h : x ∈ Set.Ico a b ∪ Set.Ico c d) :
-- imply
  x * e ∈ Set.Ico (a * e) (b * e) ∪ Set.Ico (c * e) (d * e) := by
-- proof
  simp only [Set.mem_union] at h ⊢
  obtain h | h := h
  · left
    obtain ⟨hax, hxb⟩ := h
    exact ⟨mul_le_mul_of_nonneg_right hax he.le, mul_lt_mul_of_pos_right hxb he⟩
  · right
    obtain ⟨hcx, hxd⟩ := h
    exact ⟨mul_le_mul_of_nonneg_right hcx he.le, mul_lt_mul_of_pos_right hxd he⟩


-- created on 2021-03-06
-- updated on 2023-05-20
