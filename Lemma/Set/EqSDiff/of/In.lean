import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b x : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  Icc a b \ {x} = Ico a x ∪ Ioc x b := by
-- proof
  obtain ⟨hax, hxb⟩ := h
  ext y
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Icc, Set.mem_Ico,
    Set.mem_Ioc]
  constructor
  · rintro ⟨⟨ha, hb⟩, hne⟩
    obtain hlt | hgt := lt_or_gt_of_ne hne
    · exact Or.inl ⟨ha, hlt⟩
    · exact Or.inr ⟨hgt, hb⟩
  · rintro (h | h)
    · exact ⟨⟨h.1, (h.2.trans_le hxb).le⟩, ne_of_lt h.2⟩
    · exact ⟨⟨le_trans hax h.1.le, h.2⟩, ne_of_gt h.1⟩


-- created on 2020-11-22
