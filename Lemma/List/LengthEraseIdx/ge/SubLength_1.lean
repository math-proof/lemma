import sympy.Basic


@[main]
private lemma main
  -- given
  (s : List α)
  (i : ℕ) :
-- imply
  (s.eraseIdx i).length ≥ s.length - 1 :=
-- proof
  List.le_length_eraseIdx s i


-- created on 2025-11-03
