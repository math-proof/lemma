import sympy.functions.special.tensor_functions
import Lemma.Bool.Delta.eq.Bool
open Bool


@[main]
private lemma main
  [DecidableEq α]
-- given
  (x y : α) :
-- imply
  KroneckerDelta x y = if x = y then
    1
  else
    0 := by
-- proof
  rw [Delta.eq.Bool]

  simp [Bool.toNat]


-- created on 2025-06-01
