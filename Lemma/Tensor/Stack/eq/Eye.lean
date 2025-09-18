import sympy.functions.special.tensor_functions
import sympy.matrices.expressions.special
import Lemma.Basic


@[main]
private lemma main
  [AddMonoidWithOne α] [CharZero α] :
-- imply
  [i < n] [j < n] (KroneckerDelta i j) = eye (α := α) n := by
-- proof
  unfold eye
  rfl


-- created on 2025-06-01
