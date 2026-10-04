import sympy.Basic


@[main]
private lemma main
  {s : Set α}
  {e : α}
-- given
  (h : {e} ∩ s ≠ ∅) :
-- imply
  e ∈ s := by
-- proof
  exact Set.singleton_inter_nonempty.mp (Set.nonempty_iff_ne_empty.mpr h)


-- created on 2021-04-01
