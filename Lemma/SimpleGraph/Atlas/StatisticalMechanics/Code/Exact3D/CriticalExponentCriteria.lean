import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.CriticalExponentCriteria
open StatMech StatMech.Exact3D


/--
[hasCriticalNu_of_eventually_logSlope_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CriticalExponentCriteria.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_logSlope_eq_eq
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {ν : ℝ}
-- given
  (h : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), logSlope M correlationLength β = ν) :
-- imply
  HasCriticalNu M correlationLength ν := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_of_eventually_logSlope_eq M correlationLength ν h

/--
[logSlope_eq_of_exact_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CriticalExponentCriteria.lean)
-/
@[path]
private lemma logSlope_eq_of_exact_power_eq
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {ν β : ℝ}
-- given
  (hβ : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1)
  (hξ : correlationLength β = Real.exp (-ν * Real.log (M.betaC - β))) :
-- imply
  logSlope M correlationLength β = ν := by
-- proof
  apply StatMech.Exact3D.logSlope_eq_of_exact_power M correlationLength ν β hβ hξ

/--
[hasCriticalNu_of_eventually_exact_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CriticalExponentCriteria.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_eq
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = Real.exp (-ν * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength ν := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_of_eventually_exact_power M correlationLength ν hξ


-- created on 2026-10-23
