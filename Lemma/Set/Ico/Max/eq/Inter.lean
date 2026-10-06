import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b c : ℤ} :
-- imply
  Finset.Ico (max b c) a = Finset.Ico b a ∩ Finset.Ico c a := by
-- proof
  ext x
  simp only [Finset.mem_Ico, Finset.mem_inter, max_le_iff]
  constructor
  · rintro ⟨⟨hb, hc⟩, ha⟩
    exact ⟨⟨hb, ha⟩, ⟨hc, ha⟩⟩
  · rintro ⟨⟨hb, ha⟩, ⟨hc, _⟩⟩
    exact ⟨⟨hb, hc⟩, ha⟩


-- created on 2022-01-08
