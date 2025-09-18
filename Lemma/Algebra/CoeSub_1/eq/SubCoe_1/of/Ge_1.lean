import Lemma.Basic


@[main, comm]
private lemma main
  [AddGroupWithOne α]
  {a : ℕ}
-- given
  (h : a ≥ 1) :
-- imply
  ((a - 1 : ℕ) : α) = a - 1 := by
-- proof
  have := Nat.cast_sub (R := α) h
  rw [this]
  simp_all


-- created on 2025-06-07
