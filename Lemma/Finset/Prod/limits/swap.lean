import Mathlib.Algebra.BigOperators.Ring.Finset
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {m n : ℕ}
  (f : ℕ → ℝ)
  (g : ℕ → ℕ → ℝ) :
-- imply
  ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range n, (f i + g i j)
    = ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range m, (f i + g i j) :=
-- proof
  Finset.prod_comm


-- created on 2023-11-18
-- updated on 2026-10-26
