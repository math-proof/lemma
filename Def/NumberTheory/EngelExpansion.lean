/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Finset.Nat
/-!
# Engel expansion trajectories

Remainder trajectories and length functions for Engel expansions of rationals, after
Erdős–Shallit ("New bounds on the length of finite Pierce and Engel series").
For `1 ≤ a ≤ n`, the Engel trajectory starts at `a` and iterates `t ↦ (-n) % t`
until reaching `0`; its length is the length of the Engel expansion of `a / n`.
-/


namespace EngelExpansion

/-- Negated remainder `(-n) % k` computed in `ℕ`. Equals `0` when `k ∣ n` and
`k - (n % k)` otherwise. -/
def negRem (n k : ℕ) : ℕ :=
  (k - n % k) % k

end EngelExpansion
