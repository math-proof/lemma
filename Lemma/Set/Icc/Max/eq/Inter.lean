import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b c : ℤ} :
-- imply
  Set.Icc (max b c) a = Set.Icc b a ∩ Set.Icc c a := by
-- proof
  ext x
  simp only [Set.mem_Icc, Set.mem_inter_iff, max_le_iff]
  constructor
  · rintro ⟨⟨hb, hc⟩, ha⟩
    exact ⟨⟨hb, ha⟩, ⟨hc, ha⟩⟩
  · rintro ⟨⟨hb, ha⟩, ⟨hc, _⟩⟩
    exact ⟨⟨hb, hc⟩, ha⟩


-- created on 2022-01-08
