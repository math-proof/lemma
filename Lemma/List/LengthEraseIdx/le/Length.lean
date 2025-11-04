import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  (s.eraseIdx i).length ≤ s.length :=
-- proof
  List.length_eraseIdx_le s i


-- created on 2025-11-03
