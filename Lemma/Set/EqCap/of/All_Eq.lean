import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {α : Type*}
  {n : ℕ}
  {f g : ℕ → Set α}
-- given
  (h : ∀ i < n, f i = g i) :
-- imply
  (Finset.range n).inf f = (Finset.range n).inf g := by
-- proof
  exact Finset.inf_congr rfl fun i hi => h i (Finset.mem_range.mp hi)


-- created on 2021-01-11
-- updated on 2023-05-21
