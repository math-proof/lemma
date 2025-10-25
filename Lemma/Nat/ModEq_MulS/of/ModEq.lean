import sympy.Basic


@[main]
private lemma main
  {n a b : ℕ}
-- given
  (h : a ≡ b [MOD n])
  (c : ℕ)
  (left : Bool := false) :
-- imply
  match left with
  | true =>
    c * a ≡ c * b [MOD n]
  | false =>
    a * c ≡ b * c [MOD n] := by
-- proof
  match left with
  | true =>
    exact h.mul_left c
  | false =>
    exact h.mul_right c


-- created on 2025-03-15
