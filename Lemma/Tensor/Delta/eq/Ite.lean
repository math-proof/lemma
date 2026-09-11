import Lemma.Nat.Delta.eq.Ite
import sympy.tensor.tensor
open Nat


/--
Casting a `KroneckerDelta` into a scalar tensor yields the indicator:
`↑δ_{xy} = if x = y then 1 else 0`.
-/
@[main]
private lemma main
  [AddMonoidWithOne α] [CharZero α]
  [DecidableEq β]
-- given
  (x y : β) :
-- imply
  (↑(KroneckerDelta x y) : Tensor α []) =
    if x = y then (1 : Tensor α []) else (0 : Tensor α []) := by
-- proof
  rw [Nat.Delta.eq.Ite]
  split_ifs
  · exact Nat.cast_one
  · exact Nat.cast_zero


-- created on 2026-09-11
