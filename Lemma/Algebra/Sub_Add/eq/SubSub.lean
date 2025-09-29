import sympy.Basic


@[main, comm]
private lemma nat
  (a b c : ℕ) :
-- imply
  a - (b + c) = a - b - c :=
-- proof
  Nat.sub_add_eq a b c


@[main, comm]
private lemma main
  [SubtractionCommMonoid α]
  (a b c : α) :
-- imply
  a - (b + c) = a - b - c :=
-- proof
  sub_add_eq_sub_sub a b c


-- created on 2024-07-01
