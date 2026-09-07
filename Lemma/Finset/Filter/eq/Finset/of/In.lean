import sympy.Basic


@[main]
private lemma main
  [DecidableEq ι]
  {i : ι}
  {s : Finset ι}
-- given
  (h : i ∈ s) :
-- imply
  s.filter (· = i) = {i} := by
-- proof
  simp [Finset.filter_eq', h]


-- created on 2025-10-08
