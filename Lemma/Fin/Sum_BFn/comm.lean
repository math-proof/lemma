import sympy.Basic
open Finset


@[main]
private lemma main
  [CommSemiring α]
  (m n : ℕ)
  (f : ℕ → α)
  (g : ℕ → ℕ → α) :
-- imply
  ∑ i ∈ range m, ∑ j ∈ range n, f i * g i j =
    ∑ j ∈ range n, ∑ i ∈ range m, f i * g i j := by
-- proof
  rw [Finset.sum_comm]


-- created on 2026-10-03
