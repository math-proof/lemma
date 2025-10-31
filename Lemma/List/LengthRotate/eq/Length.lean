import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  (s.rotate i).length = s.length :=
-- proof
  List.length_rotate s i


-- created on 2025-10-14
