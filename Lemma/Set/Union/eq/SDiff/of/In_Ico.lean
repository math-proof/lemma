import sympy.Basic


@[main]
private lemma main
  {i a b : ℤ}
-- given
  (h : i ∈ Set.Ico a b) :
-- imply
  Set.Ico a i ∪ Set.Ico (i + 1) b = Set.Ico a b \ {i} := by
-- proof
  ext x
  simp only [Set.mem_union, Set.mem_Ico, Set.mem_sdiff, Set.mem_singleton_iff] at h ⊢
  constructor
  ·
    intro hx
    omega
  ·
    intro hx
    omega


-- created on 2026-09-27
