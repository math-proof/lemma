import sympy.Basic


@[main]
private lemma main
-- given
  (xs : List α)
  (i : ℕ)
  (a : α)
  (j : ℕ) :
-- imply
  (xs.set i a).eraseIdx j = if j < i then
    (xs.eraseIdx j).set (i - 1) a
  else if j = i then
    xs.eraseIdx i
  else
    (xs.eraseIdx j).set i a :=
-- proof
  List.eraseIdx_set


-- created on 2025-10-07
