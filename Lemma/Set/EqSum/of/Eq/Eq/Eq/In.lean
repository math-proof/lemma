import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [DecidableEq α]
  [AddCommMonoid β]
  {y : α}
  {X : Finset α}
  {f : α → β}
-- given
  (h₀ : y ∈ X) :
-- imply
  ∑ x ∈ X, f x = f y + ∑ x ∈ X.erase y, f x :=
-- proof
  ((Finset.sum_erase_add X f h₀).symm).trans (add_comm _ _)


-- created on 2026-10-11
-- updated on 2026-10-17
