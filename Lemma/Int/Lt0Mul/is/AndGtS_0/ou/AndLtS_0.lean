import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.Lt0Mul.is.AndGtS_0.ou.AndLtS_0 |
| comm | Int.AndGtS_0.ou.AndLtS_0.is.Lt0Mul |
| mp | Int.AndGtS_0.ou.AndLtS_0.of.Lt0Mul |
| mpr | Int.Lt0Mul.of.AndGtS_0.ou.AndLtS_0 |
-/
@[main, comm, mp, mpr]
private lemma main
  [Semiring α]
  [LinearOrder α]
  [ExistsAddOfLE α]
  [PosMulStrictMono α] [MulPosStrictMono α]
  [AddLeftStrictMono α] [AddLeftReflectLT α]
-- given
  (a b : α) :
-- imply
  a * b > 0 ↔ a > 0 ∧ b > 0 ∨ a < 0 ∧ b < 0 :=
-- proof
  mul_pos_iff


-- created on 2025-04-18
