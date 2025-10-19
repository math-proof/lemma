import sympy.Basic


@[main]
private lemma main
-- given
  (l : List α)
  (n m : ℕ) :
-- imply
  (l.rotate n).rotate m = l.rotate (n + m) :=
-- proof
  List.rotate_rotate l n m


-- created on 2025-10-19
