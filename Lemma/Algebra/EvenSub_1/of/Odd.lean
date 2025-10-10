import sympy.functions.elementary.integers
import Lemma.Algebra.Odd.is.Any_Eq_AddMul2
import Lemma.Algebra.Even.is.Any_Eq_Mul2
import Lemma.Nat.EqSubAdd
open Algebra Nat


/--
the converse lemma is not true, i.e. if `n - 1` is even, it does not imply that `n` is odd.
for example, `(n : ℕ) = 0`, and `n - 1 = 0` is even, but `n` isn't odd.
-/
@[main]
private lemma main
  [IntegerRing Z]
  {n : Z}
-- given
  (h : n is odd) :
-- imply
  (n - 1) is even := by
-- proof
  let ⟨k, h⟩ := Any_Eq_AddMul2.of.Odd h
  apply Even.of.Any_Eq_Mul2
  use k
  rw [h]
  rw [EqSubAdd]


-- created on 2025-08-12
-- updated on 2025-08-13
