/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Finset.Nat
/-!
# Pierce expansion trajectories

Remainder trajectories and length functions for Pierce expansions of rationals, after
Erdős–Shallit ("New bounds on the length of finite Pierce and Engel series").
For `1 ≤ a ≤ n`, the Pierce trajectory starts at `a` and iterates `t ↦ n % t`
until reaching `0`; its length is the length of the Pierce expansion of `a / n`.
-/


namespace PierceExpansion

/-- Pierce remainder trajectory: `traj 0 = a`, `traj (j+1) = n % traj j`,
absorbing at `0`. -/
def traj (n a : ℕ) : ℕ → ℕ
  | 0 => a
  | j + 1 => if traj n a j = 0 then 0 else n % traj n a j

end PierceExpansion
