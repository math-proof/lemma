import Lemma.Basic


@[main]
private lemma MAIN'
-- given
  (s t u : Set α) :
-- imply
  (s \ t) ∩ u = (s ∩ u) \ (t ∩ u) := by
-- proof
  ext x
  simp only [Set.mem_inter_iff, Set.mem_diff, not_and]
  constructor
  ·
    rintro ⟨⟨hs, hnt⟩, hu⟩
    constructor
    .
      exact ⟨hs, hu⟩
    .
      simp_all
  ·
    rintro ⟨⟨hs, hu⟩, hntu⟩
    exact ⟨⟨hs, fun ht => hntu ht hu⟩, hu⟩



-- created on 2025-07-20
