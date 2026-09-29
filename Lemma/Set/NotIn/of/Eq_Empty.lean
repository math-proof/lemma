import sympy.Basic


@[main]
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


-- created on 2026-09-27
