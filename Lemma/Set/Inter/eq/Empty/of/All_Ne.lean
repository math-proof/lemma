import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {y : α}
  {x : ℕ → α}
-- given
  (h : ∀ i ∈ Finset.range n, x i ≠ y) :
-- imply
  {y} ∩ (⋃ i ∈ Finset.range n, {x i}) = ∅ := by
-- proof
  refine Set.singleton_inter_eq_empty.mpr fun hy => ?_
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
  exact h i hi (Set.mem_singleton_iff.mp hyi).symm


-- created on 2019-02-03
