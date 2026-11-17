/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean -/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Interval.Finset.Nat
public import Def.NumberTheory.EngelExpansion

/-!
# Engel expansion trajectories

Remainder trajectories and length functions for Engel expansions of rationals, after
Erdős–Shallit ("New bounds on the length of finite Pierce and Engel series").
For `1 ≤ a ≤ n`, the Engel trajectory starts at `a` and iterates `t ↦ (-n) % t`
until reaching `0`; its length is the length of the Engel expansion of `a / n`.
-/

public section


namespace EngelExpansion

theorem negRem_lt {n k : ℕ} (hk : k ≠ 0) : negRem n k < k := by
  simp only [negRem]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero hk)

end EngelExpansion
