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
  (h₀ : y ∉ X) :
-- imply
  ∑ x ∈ insert y X, f x = ∑ x ∈ X, f x + f y :=
-- proof
  (Finset.sum_insert h₀).trans (add_comm _ _)


-- created on 2026-10-11
-- updated on 2026-10-17
