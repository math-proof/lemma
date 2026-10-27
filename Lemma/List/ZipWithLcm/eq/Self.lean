import Theorem.Data.List.Mul.Part4


@[path]
private lemma main
-- given
  (s : List ℕ) :
-- imply
  s.zipWith Nat.lcm s = s := by
-- proof
  induction s with
  | nil =>
    rfl
  | cons n s ih =>
    simp [List.zipWith, Nat.lcm_self]


-- created on 2026-10-07
