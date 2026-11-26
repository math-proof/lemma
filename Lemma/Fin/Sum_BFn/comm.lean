import Initialize.Tactic.Attr.Basic
open Finset


@[path]
private lemma main
  [CommSemiring α]
  (m n : ℕ)
  (f : ℕ → α)
  (g : ℕ → ℕ → α) :
-- imply
  ∑ i < m, ∑ j < n, f i * g i j =
    ∑ j < n, ∑ i < m, f i * g i j := by
-- proof
  rw [Finset.sum_comm]


-- created on 2018-04-30
