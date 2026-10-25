import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCompactSupportScaling
open Filter Finset MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[isingTorusSmearedSpin_compactTorusWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCompactSupportScaling.lean)
-/
@[path]
private lemma isingTorusSmearedSpin_compactTorusWeight_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {n : Nat}
  {sigma : ConfigSpace (IsingDyadicTorus d n)} :
-- imply
  isingTorusSmearedSpin (compactTorusWeight A a n) sigma = compactWeightedSpin A a (criticalTorusLocalRestriction A n sigma) := by
-- proof
  apply StatMech.FrontierA.isingTorusSmearedSpin_compactTorusWeight A a n sigma

/--
[integral_criticalTorusCompactScaledFieldLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCompactSupportScaling.lean)
-/
@[path]
private lemma integral_criticalTorusCompactScaledFieldLaw_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {c : Nat → Real}
  {n : Nat}
  {g : BoundedContinuousFunction Real Real} :
-- imply
  (∫ x, g x ∂(criticalTorusCompactScaledFieldLaw A a c n : Measure Real)) = criticalTorusLocalObservableExpectation A (fun sigma ↦ g (c n * compactWeightedSpin A a sigma)) n := by
-- proof
  apply StatMech.FrontierA.integral_criticalTorusCompactScaledFieldLaw A a c n g

/--
[criticalTorusCompactScaledFieldLaw_tendsto_zeroGaussian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCompactSupportScaling.lean)
-/
@[path]
private lemma criticalTorusCompactScaledFieldLaw_tendsto_zeroGaussian_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {c : Nat → Real}
-- given
  (hd : 2 < d)
  (hc : Tendsto c atTop (nhds 0)) :
-- imply
  Tendsto (criticalTorusCompactScaledFieldLaw A a c) atTop (nhds (MeasureTheory.diracProba (0 : Real))) := by
-- proof
  apply StatMech.FrontierA.criticalTorusCompactScaledFieldLaw_tendsto_zeroGaussian hd A a c hc

/--
[weakLimit_eq_zeroGaussian_of_criticalTorusCompactSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCompactSupportScaling.lean)
-/
@[path]
private lemma weakLimit_eq_zeroGaussian_of_criticalTorusCompactSupport_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {c : Nat → Real}
  {mu : ProbabilityMeasure Real}
-- given
  (hd : 2 < d)
  (hc : Tendsto c atTop (nhds 0))
  (hlim : Tendsto (criticalTorusCompactScaledFieldLaw A a c) atTop (nhds mu)) :
-- imply
  (mu : Measure Real) = (MeasureTheory.diracProba (0 : Real) : ProbabilityMeasure Real) := by
-- proof
  apply StatMech.FrontierA.weakLimit_eq_zeroGaussian_of_criticalTorusCompactSupport hd A a c hc mu hlim

/--
[criticalFiniteBoxWeightedFourthScale_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCompactSupportScaling.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedFourthScale_tendsto_zero_eq
  {d : Nat}
-- given
  (hd : 2 ≤ d) :
-- imply
  Tendsto (fun n ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale d n hd) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxWeightedFourthScale_tendsto_zero hd

/--
[criticalTorusCanonicalCompactScaledFieldLaw_tendsto_zeroGaussian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCompactSupportScaling.lean)
-/
@[path]
private lemma criticalTorusCanonicalCompactScaledFieldLaw_tendsto_zeroGaussian_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
-- given
  (hd : 4 < d) :
-- imply
  Tendsto (criticalTorusCompactScaledFieldLaw A a (fun n ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale d n (by omega))) atTop (nhds (MeasureTheory.diracProba (0 : Real))) := by
-- proof
  apply StatMech.FrontierA.criticalTorusCanonicalCompactScaledFieldLaw_tendsto_zeroGaussian hd A a

/--
[weakLimit_eq_zeroGaussian_of_canonicalCriticalCompactSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCompactSupportScaling.lean)
-/
@[path]
private lemma weakLimit_eq_zeroGaussian_of_canonicalCriticalCompactSupport_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {mu : ProbabilityMeasure Real}
-- given
  (hd : 4 < d)
  (hlim : Tendsto (criticalTorusCompactScaledFieldLaw A a (fun n ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale d n (by omega))) atTop (nhds mu)) :
-- imply
  (mu : Measure Real) = (MeasureTheory.diracProba (0 : Real) : ProbabilityMeasure Real) := by
-- proof
  apply StatMech.FrontierA.weakLimit_eq_zeroGaussian_of_canonicalCriticalCompactSupport hd A a mu hlim

/--
[zeroGaussian_scalarWickMoments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCompactSupportScaling.lean)
-/
@[path]
private lemma zeroGaussian_scalarWickMoments_eq
  {d : Nat} :
-- imply
  ScalarWickMoments 0 (fun order ↦ ∫ x : Real, x ^ order ∂(MeasureTheory.diracProba (0 : Real) : ProbabilityMeasure Real)) := by
-- proof
  apply StatMech.FrontierA.zeroGaussian_scalarWickMoments


-- created on 2026-10-23
