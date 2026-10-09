import sympy.Basic


@[path, comm]
private lemma main
-- given
  (a b c : ℕ) :
-- imply
  a - (b + c) = a - b - c :=
-- proof
  Nat.sub_add_eq a b c


-- created on 2025-10-12
