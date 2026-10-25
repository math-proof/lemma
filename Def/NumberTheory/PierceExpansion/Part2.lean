/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Finset.Nat
import Theorem.NumberTheory.PierceExpansion
/-!
# Pierce expansion trajectories

Remainder trajectories and length functions for Pierce expansions of rationals, after
Erdős–Shallit ("New bounds on the length of finite Pierce and Engel series").
For `1 ≤ a ≤ n`, the Pierce trajectory starts at `a` and iterates `t ↦ n % t`
until reaching `0`; its length is the length of the Pierce expansion of `a / n`.
-/


namespace PierceExpansion

/-- Pierce length: least `j ≥ 1` with `traj j = 0`. This is the length of the Pierce
expansion of `a / n`. -/
noncomputable def length (n a : ℕ) : ℕ :=
  Nat.find (exists_traj_eq_zero_pos n a)

/-- Pierce length function: `max_{1 ≤ a ≤ n} length n a`. -/
noncomputable def maxLength (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sup (length n)

end PierceExpansion
