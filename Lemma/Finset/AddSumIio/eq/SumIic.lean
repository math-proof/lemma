import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin
import Instance.Fun
import Notation.Fun
import Syntax.Fun
import Initialize.Tactic.Attr.Basic


/--
The sum up to `k` is the sum strictly below `k`, plus the value at `k`.
-/
@[path]
private lemma main
  {n : ℕ}
-- given
  (d : Fin n ⇀ ℕ)
  (k : Fin n) :
-- imply
  (∑ t ∈ Finset.Iio k, d[t]) + d[k] =
    ∑ t ∈ Finset.Iic k, d[t] := by
-- proof
  rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self, add_comm]


-- created on 2026-10-25
