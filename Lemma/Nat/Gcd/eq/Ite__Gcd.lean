import sympy.Basic


@[main]
private lemma main
-- given
  (m n : ℕ) :
-- imply
  m.gcd n = if m = 0 then n else (n % m).gcd m := by
-- proof
  rw [Nat.gcd]


-- created on 2025-12-03
