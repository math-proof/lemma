import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h_j : s.length ≥ j)
  (h_i : i < j)
  (a : α) :
-- imply
  (s.insertIdx i a)[j]'(by grind) = s[j - 1] := by
-- proof
  have := List.get_insertIdx_add_succ s a i (j - i - 1) (by grind)
  simp_all
  grind


@[main]
private lemma fin
  {s : List α}
-- given
  (h_j : s.length ≥ j)
  (h_i : i < j)
  (a : α) :
-- imply
  (s.insertIdx i a).get ⟨j, by grind⟩ = s.get ⟨j - 1, by grind⟩ :=
-- proof
  main h_j h_i a


-- created on 2025-11-17
