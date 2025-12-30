import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {s S : Finset α}
  {e : α}
-- given
  (h : e ∈ S \ s) :
-- imply
  e ∉ s := by
-- proof
  simp_all


-- created on 2025-12-30
