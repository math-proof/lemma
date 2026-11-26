import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [DecidableEq α]
  {n : ℕ}
  {x : ℕ → Finset α}
-- given
  (h₀ : ∀ i < n, ∀ j < n, i ≠ j → x i ∩ x j = ∅) :
-- imply
  (Finset.biUnion (Finset.range n) x).card = ∑ i < n, (x i).card := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  apply Finset.card_biUnion
  intro i hi j hj hne
  exact Finset.disjoint_iff_inter_eq_empty.mpr
    (h₀ i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hne)


-- created on 2021-01-12
-- updated on 2026-10-26
