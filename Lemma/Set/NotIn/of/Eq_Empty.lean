import sympy.Basic


@[path]
private lemma main
  {x : α}
  {s : Set α}
-- given
  (h : s = ∅) :
-- imply
  x ∉ s := by
-- proof
  rw [h]
  exact Set.notMem_empty x


-- created on 2022-01-28
