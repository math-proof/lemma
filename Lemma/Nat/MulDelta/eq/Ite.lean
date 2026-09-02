import Lemma.Nat.Delta.eq.Ite
import sympy.functions.special.tensor_functions
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.MulDelta.eq.Ite |
| comm | Nat.Ite.eq.MulDelta |
-/
@[main, comm]
private lemma main
  [DecidableEq ι]
  [Semiring α]
-- given
  (x : α)
  (i j : ι) :
-- imply
  (KroneckerDelta i j : α) * x =
    if i = j then
      x
    else
      0 := by
-- proof
  by_cases h : i = j <;> simp [h, Delta.eq.Ite]


-- created on 2026-09-02
