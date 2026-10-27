import Lemma.Nat.LtSub_1.of.Le.Gt_0
open Nat Lean


/--
if index is nonnegative, it refers to the i-th element of the list
if index is negative, it refers to the (length + i)-th element of the list
-/
structure Slice where
  start : ℤ
  stop : ℤ
  step : ℤ := 1

