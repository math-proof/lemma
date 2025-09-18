import Lemma.Basic


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ⊆ B) :
-- imply
  A \ B = ∅ := by
-- proof
  -- Use the extensionality principle to show that two sets are equal if they have the same elements.
  ext x
  -- Simplify the goal using the definitions of set difference and subset.
  simp only [Set.mem_diff, Set.mem_empty_iff_false, iff_false]
  -- Introduce the hypothesis `hx` that `x` is in `A \ B`.
  intro hx
  -- Use the hypothesis `h` that `A` is a subset of `B` to derive a contradiction.
  exact hx.right (h hx.left)


-- created on 2025-04-08
