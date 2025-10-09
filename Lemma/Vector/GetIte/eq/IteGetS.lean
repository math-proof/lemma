import sympy.Basic


@[main]
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


@[main]
private lemma fin
  [Decidable p]
-- given
  (a b : List.Vector α n)
  (i : Fin n):
-- imply
  (if p then
    a.get i
  else
    b.get i) = (if p then
    a
  else
    b).get i := by
-- proof
  apply main


-- created on 2025-10-09
