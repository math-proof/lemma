import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → Finset ℤ}
-- given
  (h : ((Finset.range n).biUnion fun i => {x i}).card = n) :
-- imply
  ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n \ {i}, x i ≠ x j := by
-- proof
  rw [Finset.biUnion_singleton] at h
  have inj := Finset.card_image_iff.mp (by rw [h, Finset.card_range])
  intro i hi j hj e
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
  exact hj.2 (inj hi hj.1 e).symm


-- created on 2020-07-19
