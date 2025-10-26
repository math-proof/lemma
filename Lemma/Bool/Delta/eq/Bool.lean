import sympy.functions.special.tensor_functions
import sympy.Basic


@[main, comm]
private lemma main
  [DecidableEq α]
-- given
  (x y : α) :
-- imply
  KroneckerDelta x y = Bool.toNat (x = y) := by
-- proof
  simp [KroneckerDelta]


-- created on 2025-06-01
