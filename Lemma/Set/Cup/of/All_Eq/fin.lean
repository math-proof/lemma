import sympy.sets.sets
import sympy.Basic
open Set


@[main]
private lemma main
  {n : ℕ}
  {f g : ℕ → Set α}
-- given
  (h : ∀ i ∈ Finset.range n, f i = g i) :
-- imply
  ⋃ i ∈ Finset.range n, f i = ⋃ i ∈ Finset.range n, g i := by
-- proof
  exact Set.iUnion₂_congr h


-- created on 2026-10-03
