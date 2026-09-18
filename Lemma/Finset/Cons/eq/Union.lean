import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {s : Finset α}
  {e : α}
-- given
  (h : e ∉ s) :
-- imply
  Finset.cons e s h = s ∪ {e} := by
-- proof
  rw [Finset.cons_eq_insert, ← Finset.union_singleton]


-- created on 2026-09-18
