import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {α : Type*} [DecidableEq α]
  {n : ℕ}
  {x : ℕ → Finset α}
-- given
  (h : ∀ i < n, ∀ j < i, x i ∩ x j = ∅) :
-- imply
  (Finset.biUnion (Finset.range n) x).card = ∑ i ∈ Finset.range n, (x i).card := by
-- proof
  apply Finset.card_biUnion
  intro i hi j hj hne
  if hlt : j < i then
    exact Finset.disjoint_iff_inter_eq_empty.mpr
      (h i (Finset.mem_range.mp hi) j hlt)
  else
    have hgt : i < j := by omega
    exact (Finset.disjoint_iff_inter_eq_empty.mpr
      (h j (Finset.mem_range.mp hj) i hgt)).symm


-- created on 2020-12-23
