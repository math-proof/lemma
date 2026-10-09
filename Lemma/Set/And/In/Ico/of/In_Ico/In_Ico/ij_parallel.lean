import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {d a n m i j : ℤ}
-- given
  (hi : i ∈ Set.Ico (d + j) (n + j))
  (hj : j ∈ Set.Ico a m) :
-- imply
  i ∈ Set.Ico (d + a) (n + m - 1) ∧
    j ∈ Set.Ico (max a (i - n + 1)) (min m (i - d + 1)) := by
-- proof
  obtain ⟨hij1, hij2⟩ := hi
  obtain ⟨hja, hjm⟩ := hj
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  simp only [Set.mem_Ico, max_le_iff, lt_min_iff]
  exact ⟨⟨hja, by linarith⟩, hjm, by linarith⟩


-- created on 2020-03-20
