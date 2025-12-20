import Lemma.Int.Le0Mul.is.AndGeS_0.ou.AndLeS_0
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h : a * b ≥ 0) :
-- imply
  |a + b| = |a| + |b| := by
-- proof
  rw [abs_add_eq_add_abs_iff]
  simp [Le0Mul.is.AndGeS_0.ou.AndLeS_0] at h
  assumption


-- created on 2025-12-20
