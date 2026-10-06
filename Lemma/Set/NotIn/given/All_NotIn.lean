import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : α}
  {A : ℕ → Set α}
-- given
  (h : x ∉ ⋃ k ∈ Finset.range n, A k) :
-- imply
  ∀ k ∈ Finset.range n, x ∉ A k := by
-- proof
  simp only [Set.mem_iUnion, not_exists] at h
  exact h


-- created on 2019-02-02
