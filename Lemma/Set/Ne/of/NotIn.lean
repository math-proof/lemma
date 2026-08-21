import sympy.Basic


@[main]
private lemma main
  {e a : α}
  {s : Set α}
-- given
  (h : e ∉ insert a s) :
-- imply
  e ≠ a := by
-- proof
  intro he
  exact h (he ▸ Set.mem_insert a s)


-- created on 2023-05-20
-- updated on 2026-08-20
