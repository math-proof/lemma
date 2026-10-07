import sympy.Basic


@[main]
private lemma main
  {f : ℤ → Prop}
  {g : ℤ → ℤ → Prop}
  {a d n : ℤ} :
-- imply
  (∃ i, ∃ j, i ∈ Set.Ico (a + d) (j + d) ∧ j ∈ Set.Ico (a + 1) n ∧ f i ∧ g i j)
    ↔ ∃ j, ∃ i, j ∈ Set.Ico (i + 1 - d) n ∧ i ∈ Set.Ico (a + d) (n + d - 1) ∧ f i ∧ g i j := by
-- proof
  constructor
  ·
    rintro ⟨i, j, ⟨hi1, hi2⟩, ⟨hj1, hj2⟩, hf, hg⟩
    refine ⟨j, i, ⟨?_, hj2⟩, ⟨hi1, ?_⟩, hf, hg⟩
    ·
      omega
    ·
      omega
  ·
    rintro ⟨j, i, ⟨hj1, hj2⟩, ⟨hi1, hi2⟩, hf, hg⟩
    refine ⟨i, j, ⟨hi1, ?_⟩, ⟨?_, hj2⟩, hf, hg⟩
    ·
      omega
    ·
      omega


-- created on 2026-10-07
