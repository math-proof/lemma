import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.PressureConvex
open Finset StatMech StatMech.Ising


/--
[holder_logSumExp_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureConvex.lean)
-/
@[path]
private lemma holder_logSumExp_step_eq
  [Fintype ι]
  {c d : ι → ℝ}
  {x y a b : ℝ}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hab : a + b = 1) :
-- imply
  (∑ i, Real.exp ((a * x + b * y) * c i + d i)) ≤ (∑ i, Real.exp (x * c i + d i)) ^ a * (∑ i, Real.exp (y * c i + d i)) ^ b := by
-- proof
  apply StatMech.Ising.holder_logSumExp_step c d x y a b ha hb hab

/--
[cumulant_convexOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureConvex.lean)
-/
@[path]
private lemma cumulant_convexOn_eq
  [Fintype ι]
  [Nonempty ι]
  {c d : ι → ℝ} :
-- imply
  ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (∑ i, Real.exp (t * c i + d i))) := by
-- proof
  apply StatMech.Ising.cumulant_convexOn c d

/--
[logZ_convexOn_param](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureConvex.lean)
-/
@[path]
private lemma logZ_convexOn_param_eq
  [Fintype Ω]
  [Nonempty Ω]
  {E : Ω → ℝ} :
-- imply
  ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (Z 1 (fun s => t * E s))) := by
-- proof
  apply StatMech.Ising.logZ_convexOn_param E

/--
[isingLogZ_convexOn_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureConvex.lean)
-/
@[path]
private lemma isingLogZ_convexOn_field_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ} :
-- imply
  ConvexOn ℝ Set.univ (fun h : ℝ => Real.log (isingZ G β h)) := by
-- proof
  apply StatMech.Ising.isingLogZ_convexOn_field β

/--
[isingLogZ_convexOn_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureConvex.lean)
-/
@[path]
private lemma isingLogZ_convexOn_beta_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (h : ℝ) :
-- imply
  ConvexOn ℝ Set.univ (fun β : ℝ => Real.log (isingZ G β h)) := by
-- proof
  apply StatMech.Ising.isingLogZ_convexOn_beta h


-- created on 2026-10-23
