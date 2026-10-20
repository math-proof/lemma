import sympy.Basic


@[path]
private lemma main
  {n d a : ℕ}
  {f : ℕ → Prop}
  {g : ℕ → ℕ → Prop} :
-- imply
  (∀ j ∈ Finset.Ico (a + 1) n, ∀ i ∈ Finset.Ico (a + d) (j + d), f i ∧ g i j) ↔
    ∀ i ∈ Finset.Ico (a + d) (n + d - 1), ∀ j ∈ Finset.Ico (max (a + 1) (i - d + 1)) n, f i ∧ g i j := by
-- proof
  constructor
  ·
    intro h i hi j hj
    simp only [Finset.mem_Ico] at hi hj
    apply h
    ·
      simp only [Finset.mem_Ico]
      omega
    ·
      simp only [Finset.mem_Ico]
      omega
  ·
    intro h j hj i hi
    simp only [Finset.mem_Ico] at hi hj
    apply h
    ·
      simp only [Finset.mem_Ico]
      omega
    ·
      simp only [Finset.mem_Ico]
      omega


-- created on 2022-01-24
-- updated on 2026-10-12
