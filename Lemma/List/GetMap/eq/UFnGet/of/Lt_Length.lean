import sympy.Basic


@[main]
private lemma main
  {β : Type*}
  {s : List α}
  {f : α → β}
-- given
  (h : i < s.length) :
-- imply
  have : i < (s.map f).length := by rwa [List.length_map]
  (s.map f)[i] = f s[i] := by
-- proof
  simp


-- created on 2025-06-14
