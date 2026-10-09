import sympy.Basic


@[path]
private lemma upper.offset
  {n u i j : ℤ}
-- given
  (_h_n : n ≥ 2)
  (_h_u : u ≥ 2)
  (h_i : 0 ≤ i ∧ i < n)
  (h_j : 0 ≤ j ∧ j < n) :
-- imply
  ((j ≥ i ∧ i ≥ n + 1 - min n u) ∨ j - i ∈ Set.Ico 0 (min n u)) ∧ (j ≥ i ∨ i < n + 1 - min n u) ↔
    j - i ∈ Set.Ico 0 u := by
-- proof
  rcases le_total n u with h | h
  ·
    rw [min_eq_left h]
    simp only [Set.mem_Ico]
    omega
  ·
    rw [min_eq_right h]
    simp only [Set.mem_Ico]
    omega


@[path]
private lemma lower.offset
  {n l i j : ℤ}
-- given
  (_h_n : n ≥ 2)
  (_h_l : l ≥ 2)
  (h_i : 0 ≤ i ∧ i < n)
  (h_j : 0 ≤ j ∧ j < n) :
-- imply
  ((j < i ∧ i < min n l - 1) ∨ j - i ∈ Set.Ico (1 - min n l) 0) ∧ (j < i ∨ i ≥ min n l - 1) ↔
    j - i ∈ Set.Ico (-l + 1) 0 := by
-- proof
  rcases le_total n l with h | h
  ·
    rw [min_eq_left h]
    simp only [Set.mem_Ico]
    omega
  ·
    rw [min_eq_right h]
    simp only [Set.mem_Ico]
    omega


@[path]
private lemma upper
  {n u i j : ℤ}
-- given
  (_h_n : n ≥ 2)
  (_h_u : u ≥ 2)
  (_h_i : 0 ≤ i ∧ i < n)
  (h_j : 0 ≤ j ∧ j < n) :
-- imply
  ((j ≥ i ∧ i ≥ n - u) ∨ j - i ∈ Set.Ico 0 u) ∧ (j ≥ i ∨ i < n - u) ↔ j - i ∈ Set.Ico 0 u := by
-- proof
  simp only [Set.mem_Ico]
  omega


-- created on 2026-09-27
