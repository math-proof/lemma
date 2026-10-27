import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalNewman.Part4
open Filter Topology StatMech StatMech.FrontierA


/--
[criticalFiniteBoxNormalizedParityFourthCumulant_eq_neg_coupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalNewman.lean)
-/
@[path]
private lemma criticalFiniteBoxNormalizedParityFourthCumulant_eq_neg_coupling_eq
  {d n : Nat} :
-- imply
  criticalFiniteBoxNormalizedParityFourthCumulant d n = -criticalFiniteBoxFullRenormalizedFourthCoupling d n := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxNormalizedParityFourthCumulant_eq_neg_coupling d n

/--
[criticalFiniteBoxNormalizedParityFourthCumulant_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalNewman.lean)
-/
@[path]
private lemma criticalFiniteBoxNormalizedParityFourthCumulant_tendsto_zero_eq
  {d : Nat}
-- given
  (hd : 4 < d) :
-- imply
  Tendsto (criticalFiniteBoxNormalizedParityFourthCumulant d) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxNormalizedParityFourthCumulant_tendsto_zero d hd

/--
[scalarFourthCumulant_finiteParityTotalSpin_eq_integrated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalNewman.lean)
-/
@[path]
private lemma scalarFourthCumulant_finiteParityTotalSpin_eq_integrated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {J : Sym2 V → Real} :
-- imply
  scalarFourthCumulant (finiteParityTotalSpinFourthMoment G beta J) (finiteParityTotalSpinSecondMoment G beta J) = ∑ i : V, finiteParityIntegratedFourthCumulant G beta J i := by
-- proof
  apply StatMech.FrontierA.scalarFourthCumulant_finiteParityTotalSpin_eq_integrated G beta J

/--
[criticalFiniteBoxGlobalParityFourthCumulant_eq_scalarFourthCumulant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalNewman.lean)
-/
@[path]
private lemma criticalFiniteBoxGlobalParityFourthCumulant_eq_scalarFourthCumulant_eq
  {d n : Nat} :
-- imply
  criticalFiniteBoxGlobalParityFourthCumulant d n = scalarFourthCumulant (finiteParityTotalSpinFourthMoment (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)) (finiteParityTotalSpinSecondMoment (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)) := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxGlobalParityFourthCumulant_eq_scalarFourthCumulant d n

/--
[criticalFiniteBoxGlobalParityFourthCumulant_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalNewman.lean)
-/
@[path]
private lemma criticalFiniteBoxGlobalParityFourthCumulant_bound_eq
  {n : Nat}
-- given
  (hd : 2 ≤ d) :
-- imply
  0 ≤ -criticalFiniteBoxGlobalParityFourthCumulant d n ∧ -criticalFiniteBoxGlobalParityFourthCumulant d n ≤ (Fintype.card (sctBox d n) : Real) * (2 * criticalFreeBoxSusceptibility d (2 * n) ^ 4 + 12 * criticalFreeBoxSusceptibility d (2 * n) ^ 2) := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxGlobalParityFourthCumulant_bound hd n

/--
[criticalFiniteBoxGlobalNormalizedFourthCumulant_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalNewman.lean)
-/
@[path]
private lemma criticalFiniteBoxGlobalNormalizedFourthCumulant_bounds_eq
  {n : Nat}
-- given
  (hd : 2 ≤ d) :
-- imply
  0 ≤ -criticalFiniteBoxGlobalNormalizedFourthCumulant d n ∧ -criticalFiniteBoxGlobalNormalizedFourthCumulant d n ≤ criticalFreeBoxSusceptibility d (2 * n) ^ 2 / ((2 * n + 1 : Nat) : Real) ^ d + 6 / ((2 * n + 1 : Nat) : Real) ^ d := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxGlobalNormalizedFourthCumulant_bounds hd n

/--
[criticalFiniteBoxGlobalNormalizedFourthCumulant_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalNewman.lean)
-/
@[path]
private lemma criticalFiniteBoxGlobalNormalizedFourthCumulant_tendsto_zero_eq
  {d : Nat}
-- given
  (hd : 4 < d) :
-- imply
  Tendsto (criticalFiniteBoxGlobalNormalizedFourthCumulant d) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxGlobalNormalizedFourthCumulant_tendsto_zero d hd

/--
[criticalFiniteBoxCumulantLimits_of_newmanFourthControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalNewman.lean)
-/
@[path]
private lemma criticalFiniteBoxCumulantLimits_of_newmanFourthControl_eq
  {d : Nat}
  {cumulants : Nat → Nat → Real}
  {variance : Real}
-- given
  (hd : 4 < d)
  (hcontrol : NewmanFourthCumulantControl cumulants)
  (hvariance : Tendsto (fun n => cumulants n 2) atTop (nhds variance))
  (hfourth : ∀ n, cumulants n 4 = criticalFiniteBoxNormalizedParityFourthCumulant d n) :
-- imply
  ∀ order, Tendsto (fun n => cumulants n order) atTop (nhds (scalarGaussianCumulant variance order)) := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxCumulantLimits_of_newmanFourthControl d hd cumulants variance hcontrol hvariance hfourth

/--
[criticalFiniteBoxScalarWickMoments_of_newmanFourthControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalNewman.lean)
-/
@[path]
private lemma criticalFiniteBoxScalarWickMoments_of_newmanFourthControl_eq
  {d : Nat}
  {moments cumulants : Nat → Nat → Real}
  {limitMoments : Nat → Real}
  {variance : Real}
-- given
  (hd : 4 < d)
  (hrecurrence : HasScalarMomentCumulantRecurrence moments cumulants)
  (hmoments : ∀ order, Tendsto (fun n => moments n order) atTop (nhds (limitMoments order)))
  (hcontrol : NewmanFourthCumulantControl cumulants)
  (hvariance : Tendsto (fun n => cumulants n 2) atTop (nhds variance))
  (hfourth : ∀ n, cumulants n 4 = criticalFiniteBoxNormalizedParityFourthCumulant d n) :
-- imply
  ScalarWickMoments variance limitMoments := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxScalarWickMoments_of_newmanFourthControl d hd moments cumulants limitMoments variance hrecurrence hmoments hcontrol hvariance hfourth


-- created on 2026-10-23
