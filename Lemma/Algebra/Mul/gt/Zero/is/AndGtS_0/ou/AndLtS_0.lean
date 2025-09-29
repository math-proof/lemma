import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [Semiring α]
  [LinearOrder α]
  [ExistsAddOfLE α]
  [PosMulStrictMono α]
  [MulPosStrictMono α]
  [AddLeftStrictMono α]
  [AddLeftReflectLT α]
  {a b : α} :
-- imply
  a * b > 0 ↔ a > 0 ∧ b > 0 ∨ a < 0 ∧ b < 0 :=
-- proof
  mul_pos_iff


-- created on 2025-04-18
