import sympy.functions.elementary.complexes
import sympy.Basic
open Real


@[main]
private lemma main
  {n : ℕ}
  {f g : ℕ → Set ℤ}
-- given
  (h : ∀ i ∈ Finset.range n, f i ⊆ g i) :
-- imply
  ⋃ i ∈ Finset.range n, f i ⊆ ⋃ i ∈ Finset.range n, g i := by
-- proof
  exact Set.iUnion₂_mono h


-- created on 2026-09-27
