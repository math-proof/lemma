import sympy.Basic


@[main]
private lemma main
  {a : α}
  {s : Set α}
-- given
  (h : a ∈ s) :
-- imply
  {a} ⊆ s := by
-- proof
  -- Use the theorem `Set.singleton_subset_iff` to rewrite the goal as `a ∈ s`
  rw [Set.singleton_subset_iff]
  -- Since `a ∈ s` is given by hypothesis `h`, we can directly conclude the proof
  exact h


-- created on 2025-05-18
