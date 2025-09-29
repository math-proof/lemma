import stdlib.List.Vector
import sympy.Basic


@[main]
private lemma main
  [Add α] [Zero α]
  {l : List α}
  {a : α} :
-- imply
  (a :: l).sum = a + l.sum :=
-- proof
  List.sum_cons


@[main]
private lemma vector
  [Add α] [Zero α]
  {l : List.Vector α n}
  {a : α} :
-- imply
  (a ::ᵥ l).sum = a + l.sum :=
-- proof
  main

-- created on 2024-07-01
-- updated on 2025-05-08
