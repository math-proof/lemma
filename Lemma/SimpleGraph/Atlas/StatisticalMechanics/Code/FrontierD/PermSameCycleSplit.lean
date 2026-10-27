import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.PermSameCycleSplit
open Equiv StatMech StatMech.FrontierD


/--
[sameCycle_mul_swap_partition_of_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/PermSameCycleSplit.lean)
-/
@[path]
private lemma sameCycle_mul_swap_partition_of_count_eq
  [Fintype D]
  [DecidableEq D]
  {σ : Perm D}
  {a b : D}
  {x : D}
-- given
  (habne : a ≠ b)
  (hab : σ.SameCycle a b)
  (hcount : permCycleCount (σ * Equiv.swap a b) = permCycleCount σ + 1) :
-- imply
  σ.SameCycle a x ↔ (σ * Equiv.swap a b).SameCycle a x ∨ (σ * Equiv.swap a b).SameCycle b x := by
-- proof
  apply StatMech.FrontierD.sameCycle_mul_swap_partition_of_count σ habne hab hcount x

/--
[sameCycle_mul_swap_iff_of_not_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/PermSameCycleSplit.lean)
-/
@[path]
private lemma sameCycle_mul_swap_iff_of_not_sameCycle_eq
  [Fintype D]
  [DecidableEq D]
  {σ : Perm D}
  {a b : D}
  {x y : D}
-- given
  (habne : a ≠ b)
  (hab : σ.SameCycle a b)
  (hcount : permCycleCount (σ * Equiv.swap a b) = permCycleCount σ + 1)
  (hx : ¬ σ.SameCycle a x) :
-- imply
  (σ * Equiv.swap a b).SameCycle x y ↔ σ.SameCycle x y := by
-- proof
  apply StatMech.FrontierD.sameCycle_mul_swap_iff_of_not_sameCycle σ habne hab hcount hx


-- created on 2026-10-23
