import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [DecidableEq α]
  {n : ℕ}
  {x : ℕ → Finset α}
-- given
  (h₀ : ∀ i < n, ∀ j < n, i ≠ j → x i ∩ x j = ∅) :
-- imply
  (Finset.biUnion (Finset.range n) x).card = ∑ i ∈ Finset.range n, (x i).card := by
-- proof
  apply Finset.card_biUnion
  intro i hi j hj hne
  exact Finset.disjoint_iff_inter_eq_empty.mpr
    (h₀ i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hne)


-- created on 2026-10-11
-- updated on 2026-10-17
