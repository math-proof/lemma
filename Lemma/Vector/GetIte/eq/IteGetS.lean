import sympy.Basic


@[main, fin]
private lemma main
  [Decidable p]
-- given
  (a b : List.Vector α n)
  (i : Fin n):
-- imply
  (if p then
    a[i]
  else
    b[i]) = (if p then
    a
  else
    b)[i] := by
-- proof
  split_ifs with h <;> rfl


-- created on 2025-10-09
