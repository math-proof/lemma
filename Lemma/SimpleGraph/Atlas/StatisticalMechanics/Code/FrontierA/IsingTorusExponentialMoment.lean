import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusExponentialMoment
open Finset StatMech StatMech.FrontierA


/--
[isingTorus_bilinear_expMoment_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusExponentialMoment.lean)
-/
@[path]
private lemma isingTorus_bilinear_expMoment_le_eq
  {d k : Nat}
  {beta : Real}
  {t : Real}
-- given
  (hdom : IsingTorusGaussianDominated (d := d) (k := k) beta)
  (h : IsingDyadicTorus d k -> Real) :
-- imply
  (∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * Real.exp (-beta * t * isingTorusDirichletBilinear (isingTorusSpinField sigma) h)) / isingTorusShiftedPartition (d := d) (k := k) beta 0 <= Real.exp ((beta / 2) * t ^ 2 * isingTorusDirichlet h) := by
-- proof
  apply StatMech.FrontierA.isingTorus_bilinear_expMoment_le beta hdom t h

/--
[isingTorus_bilinear_expMoment_le_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusExponentialMoment.lean)
-/
@[path]
private lemma isingTorus_bilinear_expMoment_le_unconditional_eq
  {d k : Nat}
  {beta : Real}
  {t : Real}
-- given
  (hbeta : 0 < beta)
  (h : IsingDyadicTorus d k -> Real) :
-- imply
  (∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * Real.exp (-beta * t * isingTorusDirichletBilinear (isingTorusSpinField sigma) h)) / isingTorusShiftedPartition (d := d) (k := k) beta 0 <= Real.exp ((beta / 2) * t ^ 2 * isingTorusDirichlet h) := by
-- proof
  apply StatMech.FrontierA.isingTorus_bilinear_expMoment_le_unconditional beta hbeta t h

/--
[isingTorus_bilinear_expAbsMoment_le_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusExponentialMoment.lean)
-/
@[path]
private lemma isingTorus_bilinear_expAbsMoment_le_unconditional_eq
  {d k : Nat}
  {beta : Real}
  {s : Real}
-- given
  (hbeta : 0 < beta)
  (h : IsingDyadicTorus d k -> Real) :
-- imply
  (∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * Real.exp (s * |beta * isingTorusDirichletBilinear (isingTorusSpinField sigma) h|)) / isingTorusShiftedPartition (d := d) (k := k) beta 0 <= 2 * Real.exp ((beta / 2) * s ^ 2 * isingTorusDirichlet h) := by
-- proof
  apply StatMech.FrontierA.isingTorus_bilinear_expAbsMoment_le_unconditional beta hbeta s h


-- created on 2026-10-23
