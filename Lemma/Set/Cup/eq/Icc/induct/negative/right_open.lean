import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ} :
-- imply
  ⋃ k < n, Set.Ico (-(k : ℤ) - 1) (-(k : ℤ)) = Set.Ico (-(n : ℤ)) 0 := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Set.biUnion_lt_succ, ih]
    ext x
    simp only [Set.mem_union, Set.mem_Ico]
    push_cast
    omega


-- created on 2021-02-12
