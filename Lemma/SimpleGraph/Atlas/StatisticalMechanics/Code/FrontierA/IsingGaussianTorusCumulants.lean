import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianTorusCumulants.Part2
open Filter MeasureTheory Topology StatMech StatMech.FrontierA


/--
[isingTorusZeroFieldMass_eq_finiteIsingWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusCumulants.lean)
-/
@[path]
private lemma isingTorusZeroFieldMass_eq_finiteIsingWeight_eq
  {d k : Nat}
  {beta : Real}
  {sigma : ConfigSpace (IsingDyadicTorus d k)} :
-- imply
  isingTorusZeroFieldMass beta sigma = zeroFieldInteractionWeight (isingTorusGraph d k) beta sigma / ∑ tau : ConfigSpace (IsingDyadicTorus d k), zeroFieldInteractionWeight (isingTorusGraph d k) beta tau := by
-- proof
  apply StatMech.FrontierA.isingTorusZeroFieldMass_eq_finiteIsingWeight beta sigma

/--
[integral_pow_isingTorusSmearedSpin_eq_finiteIsingWeightedRawMoment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusCumulants.lean)
-/
@[path]
private lemma integral_pow_isingTorusSmearedSpin_eq_finiteIsingWeightedRawMoment_eq
  {d k : Nat}
  {beta : Real}
  {a : IsingDyadicTorus d k → Real}
  {order : Nat} :
-- imply
  (∫ sigma, isingTorusSmearedSpin a sigma ^ order ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta : ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)))) = finiteIsingWeightedRawMoment (isingTorusGraph d k) beta a order := by
-- proof
  apply StatMech.FrontierA.integral_pow_isingTorusSmearedSpin_eq_finiteIsingWeightedRawMoment beta a order

/--
[integral_pow_projection_isingTorusScaledSmearedFieldLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusCumulants.lean)
-/
@[path]
private lemma integral_pow_projection_isingTorusScaledSmearedFieldLaw_eq
  {d k : Nat}
  {beta c t : Real}
  {a : IsingDyadicTorus d k → Real}
  {order : Nat} :
-- imply
  (∫ x, x ^ order ∂(((isingTorusFieldLaw d k beta (isingTorusScaledSmearedField c a)).map (InnerProductSpace.toDualMap Real Real t).continuous.measurable.aemeasurable) : Measure Real)) = (t * c) ^ order * finiteIsingWeightedRawMoment (isingTorusGraph d k) beta a order := by
-- proof
  apply StatMech.FrontierA.integral_pow_projection_isingTorusScaledSmearedFieldLaw beta c t a order

/--
[isingTorusScaledSmeared_hasScalarMomentCumulantRecurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusCumulants.lean)
-/
@[path]
private lemma isingTorusScaledSmeared_hasScalarMomentCumulantRecurrence_eq
  {d k : Nat}
  {d : Nat}
  {beta : Real}
  {c : Nat → Real}
  {a : (k : Nat) → IsingDyadicTorus d k → Real}
  {t : Real} :
-- imply
  HasScalarMomentCumulantRecurrence (fun k order => ∫ x, x ^ order ∂(((isingTorusFieldLaw d k beta (isingTorusScaledSmearedField (c k) (a k))).map (InnerProductSpace.toDualMap Real Real t).continuous.measurable.aemeasurable) : Measure Real)) (fun k order => isingTorusScaledSmearedCumulant beta (c k) t (a k) order) := by
-- proof
  apply StatMech.FrontierA.isingTorusScaledSmeared_hasScalarMomentCumulantRecurrence d beta c a t

/--
[isingTorusScaledSmeared_newmanFourthCumulantControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusCumulants.lean)
-/
@[path]
private lemma isingTorusScaledSmeared_newmanFourthCumulantControl_eq
  {d k : Nat}
  {d : Nat}
  {beta : Real}
  {c : Nat → Real}
  {a : (k : Nat) → IsingDyadicTorus d k → Real}
  {t : Real}
-- given
  (hbeta : 0 ≤ beta)
  (ha : ∀ k x, 0 < a k x) :
-- imply
  NewmanFourthCumulantControl (fun k order => isingTorusScaledSmearedCumulant beta (c k) t (a k) order) := by
-- proof
  apply StatMech.FrontierA.isingTorusScaledSmeared_newmanFourthCumulantControl d beta hbeta c a ha t

/--
[finiteIsingWeighted_physical_newmanFourthCumulantControl_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusCumulants.lean)
-/
@[path]
private lemma finiteIsingWeighted_physical_newmanFourthCumulantControl_unconditional_eq
  {d k : Nat}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Nat → Real}
  {a : Nat → V → Real}
-- given
  (hbeta : ∀ n, 0 ≤ beta n)
  (ha : ∀ n v, 0 < a n v) :
-- imply
  NewmanFourthCumulantControl (fun n order => PhysicalIsing.finiteIsingWeightedCumulant G (beta n) (a n) order) := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeighted_physical_newmanFourthCumulantControl_unconditional G beta hbeta a ha


-- created on 2026-10-23
