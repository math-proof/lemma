import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [Ring α]
  [LinearOrder α]
  [PosMulStrictMono α]
  [MulPosStrictMono α]
  [AddLeftReflectLT α]
  [AddLeftStrictMono α]
-- given
  (a b : α) :
-- imply
  a * b < 0 ↔ a < 0 ∧ b > 0 ∨ b < 0 ∧ a > 0 := by
-- proof
  rw [Or.comm]
  rw [And.comm]
  apply mul_neg_iff


-- created on 2025-03-30
