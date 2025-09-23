import Lemma.Basic


@[main]
private lemma main
  [CommSemiring α]
  {a b : α}
  {n : ℕ} :
-- imply
  (a * b) ^ n = a ^ n * b ^ n := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ih]
    ring


-- created on 2024-07-01
-- updated on 2025-01-26
