import sympy.Basic


@[path]
private lemma main
-- given
  (a b x : ℕ) :
-- imply
  x % (a * b) = x % a + a * (x / a % b) :=
-- proof
  Nat.mod_mul


-- created on 2025-11-21
