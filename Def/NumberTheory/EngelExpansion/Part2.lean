/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean -/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Interval.Finset.Nat
public import Theorem.NumberTheory.EngelExpansion

@[expose] public section

/-!
# Engel expansion trajectories

Remainder trajectories and length functions for Engel expansions of rationals, after
Erdős–Shallit ("New bounds on the length of finite Pierce and Engel series").
For `1 ≤ a ≤ n`, the Engel trajectory starts at `a` and iterates `t ↦ (-n) % t`
until reaching `0`; its length is the length of the Engel expansion of `a / n`.
-/


namespace EngelExpansion

/-- Engel remainder trajectory: `traj 0 = a`, `traj (j+1) = negRem n (traj j)`,
absorbing at `0`. -/
def traj (n a : ℕ) : ℕ → ℕ
  | 0 => a
  | j + 1 => if traj n a j = 0 then 0 else negRem n (traj n a j)

end EngelExpansion
