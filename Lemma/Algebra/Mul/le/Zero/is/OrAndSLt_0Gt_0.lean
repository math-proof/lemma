import sympy.Basic


@[main]
private lemma main
  [Ring α]
  [LinearOrder α]
  [MulPosStrictMono α]
  [PosMulStrictMono α]
  [AddLeftReflectLE α]
  [AddLeftMono α]
  {a b : α} :
-- imply
  a * b ≤ 0 ↔ a ≤ 0 ∧ b ≥ 0 ∨ b ≤ 0 ∧ a ≥ 0 := by
-- proof
  rw [Or.comm]
  rw [And.comm]
  apply mul_nonpos_iff


-- created on 2025-03-29
-- updated on 2025-03-30
