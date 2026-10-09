import sympy.Basic


@[path]
private lemma main
  {e : α}
  {U A : Set α}
-- given
  (h : e ∉ U \ A) :
-- imply
  e ∉ U ∨ e ∈ A :=
-- proof
  (not_and_or.mp h).imp id not_not.mp


-- created on 2020-10-01
