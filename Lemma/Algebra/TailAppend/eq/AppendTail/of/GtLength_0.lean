import sympy.Basic


@[main]
private lemma main
  {a : List α}
-- given
  (h : a.length > 0)
  (b : List α) :
-- imply
  (a ++ b).tail = a.tail ++ b := by
-- proof
  match a with
  | [] =>
    contradiction
  | a₀ :: a =>
    simp


-- created on 2025-07-06
