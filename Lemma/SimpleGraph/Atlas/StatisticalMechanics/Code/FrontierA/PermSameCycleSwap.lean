import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.PermSameCycleSwap
open Equiv StatMech StatMech.FrontierA


/--
[sameCycle_mono_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/PermSameCycleSwap.lean)
-/
@[path]
private lemma sameCycle_mono_of_step_eq
  [Fintype D]
  [DecidableEq D]
  {sigma tau : Perm D}
  {x y : D}
-- given
  (hstep : forall x, sigma.SameCycle x (tau x))
  (hxy : tau.SameCycle x y) :
-- imply
  sigma.SameCycle x y := by
-- proof
  apply StatMech.FrontierA.sameCycle_mono_of_step sigma tau hstep hxy

/--
[permCycleCount_eq_of_sameCycle_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/PermSameCycleSwap.lean)
-/
@[path]
private lemma permCycleCount_eq_of_sameCycle_iff_eq
  [Fintype D]
  [DecidableEq D]
  {sigma tau : Perm D}
-- given
  (h : forall x y, sigma.SameCycle x y <-> tau.SameCycle x y) :
-- imply
  permCycleCount sigma = permCycleCount tau := by
-- proof
  apply StatMech.FrontierA.permCycleCount_eq_of_sameCycle_iff sigma tau h

/--
[not_sameCycle_mul_swap_of_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/PermSameCycleSwap.lean)
-/
@[path]
private lemma not_sameCycle_mul_swap_of_sameCycle_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Perm D}
  {a b : D}
-- given
  (hne : a ≠ b)
  (hab : sigma.SameCycle a b) :
-- imply
  ¬((sigma * Equiv.swap a b).SameCycle a b) := by
-- proof
  apply StatMech.FrontierA.not_sameCycle_mul_swap_of_sameCycle sigma hne hab


-- created on 2026-10-23
