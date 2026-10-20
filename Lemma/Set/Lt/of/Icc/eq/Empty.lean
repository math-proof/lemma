import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h₀ : Set.Icc a b = ∅) :
-- imply
  b < a :=
-- proof
  lt_of_not_ge (Set.Icc_eq_empty_iff.mp h₀)


-- created on 2021-05-06
-- updated on 2026-10-17
