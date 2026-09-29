import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {n : ℕ}
  {x : ℕ → α}
-- given
  (h : ((Finset.range n).image x).card = n) :
-- imply
  ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range i, x i ≠ x j := by
-- proof
  intro i hi j hj e
  rw [Finset.mem_range] at hi hj
  have hinj : Set.InjOn x (Finset.range n) := by
    rw [← Finset.card_image_iff, h, Finset.card_range]
  have := hinj (Finset.mem_coe.mpr (Finset.mem_range.mpr hi)) (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) e
  omega


-- created on 2026-09-27
