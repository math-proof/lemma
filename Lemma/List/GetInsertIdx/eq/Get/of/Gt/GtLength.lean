import sympy.Basic


@[main, fin]
private lemma main
  {s : List α}
-- given
  (h : s.length > j)
  (h_ij : i > j)
  (a : α) :
-- imply
  (s.insertIdx i a)[j]'(by grind) = s[j] := by
-- proof
  apply List.get_insertIdx_of_lt (hn := h_ij)


-- created on 2025-10-09
