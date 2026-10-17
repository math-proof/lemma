import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic


@[path]
private lemma main
  {α : Type} [DecidableEq α]
  (A : Finset α)
  (f g : α → ℝ) :
-- imply
  ∑ x ∈ A.filter (fun x => 0 < g x), f x
    = ∑ x ∈ A, if 0 < g x then f x else 0 :=
-- proof
  Finset.sum_filter (fun x => 0 < g x) f


-- created on 2026-10-11
-- updated on 2026-10-17
