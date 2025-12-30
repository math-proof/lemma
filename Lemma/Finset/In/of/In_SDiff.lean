import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {s U : Finset α}
  {x : α}
-- given
  (h : x ∈ U \ s) :
-- imply
  x ∈ U := by
-- proof
  simp_all


-- created on 2025-12-30
