import sympy.Basic
import sympy.sets.sets


@[main]
private lemma main
  {α : Type*}
  {S : Set α}
  {f : α → ℝ}
-- given
  (hbdd : BddAbove (f '' S)) :
-- imply
  ∀ x ∈ S, sSup (f '' S) ≥ f x := by
-- proof
  intro x hx
  exact le_csSup hbdd (Set.mem_image_of_mem f hx)


-- created on 2026-09-26
