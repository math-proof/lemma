import sympy.Basic


@[main]
private lemma main
  {a : List α}
-- given
  (h : a ≠ [])
  (b : List α) :
-- imply
  (a ++ b).tail = a.tail ++ b := by
-- proof
  match a with
  | [] =>
    contradiction
  | a₀ :: a =>
    simp


-- created on 2026-01-12
