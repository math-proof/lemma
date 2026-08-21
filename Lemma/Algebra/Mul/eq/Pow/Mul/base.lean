import sympy.Basic


@[main]
private lemma main
  [CommMonoid α]
  {a b : α}
  {n : ℕ} :
-- imply
  a ^ n * b ^ n = (a * b) ^ n :=
-- proof
  (mul_pow a b n).symm


-- created on 2018-11-13
-- updated on 2026-08-20
