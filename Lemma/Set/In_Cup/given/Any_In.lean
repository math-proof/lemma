import sympy.sets.sets
import sympy.Basic
open Set


@[main]
private lemma main
  {n : ℕ}
  {A : ℕ → Set α}
  {x : α}
-- given
  (h : x ∈ ⋃ i ∈ Finset.range n, A i) :
-- imply
  ∃ i, i ∈ Finset.range n ∧ x ∈ A i := by
-- proof
  simpa [mem_iUnion₂] using h


-- created on 2026-10-03
