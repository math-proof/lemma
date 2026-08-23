import sympy.Basic


@[main]
private lemma main
  [CommMonoid α]
  {a b : α}
  {n : ℕ} :
-- imply
  (a * b) ^ n = a ^ n * b ^ n :=
-- proof
  mul_pow a b n


-- created on 2024-07-01
-- updated on 2025-01-26
