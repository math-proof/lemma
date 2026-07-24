import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s.take 1 = [s[0]] := by
-- proof
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_length_pos h
  rfl


-- created on 2025-06-17
