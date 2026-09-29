import sympy.Basic


@[main]
private lemma transform.ij_parallel
  {i j a m d n : ℤ} :
-- imply
  i ∈ Set.Ico (d + j) (n + j) ∧ j ∈ Set.Ico a m ↔ i ∈ Set.Ico (d + a) (n + m - 1) ∧ j ∈ Set.Ico (max a (i - n + 1)) (min m (i - d + 1)) := by
-- proof
  simp only [Set.mem_Ico, max_le_iff, lt_min_iff]
  constructor
  ·
    intro h
    omega
  ·
    intro h
    omega


-- created on 2026-09-27
