import sympy.Basic


@[main]
private lemma main
  [DecidableEq α] [AddCommGroup β]
  {n : ℕ}
  {y : α}
  {x : ℕ → α}
  {f : α → β}
-- given
  (h : ∀ i ∈ Finset.range n, y ≠ x i) :
-- imply
  ∑ t ∈ (Finset.range n).image x, f t = ∑ t ∈ (Finset.range n).image x ∪ {y}, f t - f y := by
-- proof
  have hy : y ∉ (Finset.range n).image x := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro i hi e
    exact h i hi e.symm
  rw [Finset.sum_union (Finset.disjoint_singleton_right.mpr hy), Finset.sum_singleton, add_sub_cancel_right]


@[main]
private lemma double_limits
  [DecidableEq α] [AddCommMonoid β]
  {n : ℕ}
  {a : ℕ → α}
  {f : α → β}
-- given
  (h : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range i, a i ≠ a j) :
-- imply
  ∑ x ∈ (Finset.range n).image a, f x = ∑ i ∈ Finset.range n, f (a i) := by
-- proof
  apply Finset.sum_image
  intro i hi j hj e
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases lt_trichotomy i j with hij | hij | hij
  ·
    exact absurd e.symm (h j (Finset.mem_range.mpr hj) i (Finset.mem_range.mpr hij))
  ·
    exact hij
  ·
    exact absurd e (h i (Finset.mem_range.mpr hi) j (Finset.mem_range.mpr hij))


-- created on 2019-02-04
