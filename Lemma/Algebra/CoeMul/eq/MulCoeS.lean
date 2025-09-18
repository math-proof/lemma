import Lemma.Basic


@[main, comm]
private lemma nat
  [NonAssocSemiring α]
  {a b : ℕ} :
-- imply
  ((a * b : ℕ) : α) = a * b :=
-- proof
  Nat.cast_mul a b


@[main, comm]
private lemma main
  [NonAssocRing α]
  {a b : ℤ} :
-- imply
  ((a * b : ℤ) : α) = a * b :=
-- proof
  Int.cast_mul a b


-- created on 2025-03-30
-- updated on 2025-04-20
