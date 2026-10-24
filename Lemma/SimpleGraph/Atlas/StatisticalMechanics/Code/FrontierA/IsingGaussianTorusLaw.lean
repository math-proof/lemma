import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingGaussianTorusLaw
open Finset MeasureTheory StatMech StatMech.FrontierA


/--
[isingTorusZeroFieldMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusLaw.lean)
-/
@[path]
private lemma isingTorusZeroFieldMass_nonneg_eq
  {d k : Nat}
  {beta : Real} :
-- imply
  0 <= isingTorusZeroFieldMass (d := d) (k := k) beta := by
-- proof
  apply StatMech.FrontierA.isingTorusZeroFieldMass_nonneg beta

/--
[sum_isingTorusZeroFieldMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusLaw.lean)
-/
@[path]
private lemma sum_isingTorusZeroFieldMass_eq
  {d k : Nat}
  {beta : Real} :
-- imply
  ∑ sigma : ConfigSpace (IsingDyadicTorus d k), isingTorusZeroFieldMass beta sigma = 1 := by
-- proof
  apply StatMech.FrontierA.sum_isingTorusZeroFieldMass beta

/--
[isingTorusZeroFieldLaw_real_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusLaw.lean)
-/
@[path]
private lemma isingTorusZeroFieldLaw_real_singleton_eq
  {d k : Nat}
  {beta : Real}
  {sigma : ConfigSpace (IsingDyadicTorus d k)} :
-- imply
  ((isingTorusZeroFieldLaw (d := d) (k := k) beta : ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k))) : Measure (ConfigSpace (IsingDyadicTorus d k))).real {sigma} = isingTorusZeroFieldMass beta sigma := by
-- proof
  apply StatMech.FrontierA.isingTorusZeroFieldLaw_real_singleton beta sigma

/--
[integral_isingTorusZeroFieldLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusLaw.lean)
-/
@[path]
private lemma integral_isingTorusZeroFieldLaw_eq
  {d k : Nat}
  {beta : Real}
-- given
  (g : ConfigSpace (IsingDyadicTorus d k) -> Real) :
-- imply
  ∫ sigma, g sigma ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta : ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k))) = ∑ sigma : ConfigSpace (IsingDyadicTorus d k), isingTorusZeroFieldMass beta sigma * g sigma := by
-- proof
  apply StatMech.FrontierA.integral_isingTorusZeroFieldLaw beta g

/--
[integral_exp_isingTorusSmearedSpin_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusLaw.lean)
-/
@[path]
private lemma integral_exp_isingTorusSmearedSpin_le_eq
  {d k : Nat}
  {beta : Real}
  {s : Real}
-- given
  (hbeta : 0 < beta)
  (f h : IsingDyadicTorus d k -> Real)
  (hpotential : forall u : IsingDyadicTorus d k -> Real, isingTorusDirichletBilinear u h = ∑ x, u x * f x) :
-- imply
  (∫ sigma, Real.exp (s * isingTorusSmearedSpin f sigma) ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta : ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)))) <= Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta)) := by
-- proof
  apply StatMech.FrontierA.integral_exp_isingTorusSmearedSpin_le beta hbeta f h hpotential s

/--
[integral_exp_abs_isingTorusSmearedSpin_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusLaw.lean)
-/
@[path]
private lemma integral_exp_abs_isingTorusSmearedSpin_le_eq
  {d k : Nat}
  {beta : Real}
  {s : Real}
-- given
  (hbeta : 0 < beta)
  (f h : IsingDyadicTorus d k -> Real)
  (hpotential : forall u : IsingDyadicTorus d k -> Real, isingTorusDirichletBilinear u h = ∑ x, u x * f x) :
-- imply
  (∫ sigma, Real.exp (s * |isingTorusSmearedSpin f sigma|) ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta : ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)))) <= 2 * Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta)) := by
-- proof
  apply StatMech.FrontierA.integral_exp_abs_isingTorusSmearedSpin_le beta hbeta f h hpotential s

/--
[exists_isingTorusSmearedSpin_expMoment_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusLaw.lean)
-/
@[path]
private lemma exists_isingTorusSmearedSpin_expMoment_bounds_eq
  {d k : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (f : IsingDyadicTorus d k -> Real)
  (hzero : ∑ x, f x = 0) :
-- imply
  ∃ h : IsingDyadicTorus d k -> Real, (forall u : IsingDyadicTorus d k -> Real, isingTorusDirichletBilinear u h = ∑ x, u x * f x) ∧ (forall s : Real, (∫ sigma, Real.exp (s * isingTorusSmearedSpin f sigma) ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta : ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)))) <= Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta))) ∧ (forall s : Real, (∫ sigma, Real.exp (s * |isingTorusSmearedSpin f sigma|) ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta : ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)))) <= 2 * Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta))) := by
-- proof
  apply StatMech.FrontierA.exists_isingTorusSmearedSpin_expMoment_bounds beta hbeta f hzero


-- created on 2026-10-23
