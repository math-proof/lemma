import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ} :
-- imply
  ⋃ k < n, Set.Ico (k : ℤ) ((k : ℤ) + 1) = Set.Ico (0 : ℤ) (n : ℤ) := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Set.biUnion_lt_succ, ih]
    ext x
    simp only [Set.mem_union, Set.mem_Ico]
    omega


-- created on 2021-02-12
