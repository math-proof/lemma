import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b c : ℤ} :
-- imply
  Set.Ioc a (min b c) = Set.Ioc a b ∩ Set.Ioc a c := by
-- proof
  ext x
  simp only [Set.mem_Ioc, Set.mem_inter_iff, le_min_iff]
  constructor
  · rintro ⟨ha, hb, hc⟩
    exact ⟨⟨ha, hb⟩, ⟨ha, hc⟩⟩
  · rintro ⟨⟨ha, hb⟩, ⟨_, hc⟩⟩
    exact ⟨ha, hb, hc⟩


-- created on 2022-01-08
