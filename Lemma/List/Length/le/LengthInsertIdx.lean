import sympy.Basic


@[main]
private lemma main
  -- given
  (l : List α)
  (x : α)
  (i : ℕ) :
-- imply
  l.length ≤ (l.insertIdx i x).length :=
-- proof
  List.length_le_length_insertIdx


-- created on 2025-12-31
