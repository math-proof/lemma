import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSpinConformalReduction
open BoundedContinuousFunction Filter MeasureTheory Topology StatMech StatMech.FrontierA


/--
[spinProdBCF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinConformalReduction.lean)
-/
@[path]
private lemma spinProdBCF_apply_eq
  {d : Nat}
  {A : Finset (Site d)}
  {omega : ConfigSpace (Site d)} :
-- imply
  spinProdBCF A omega = spinProd A omega := by
-- proof
  apply StatMech.FrontierA.spinProdBCF_apply A omega

/--
[WeakConvergesTo.tendsto_integral_spinProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinConformalReduction.lean)
-/
@[path]
private lemma tendsto_integral_spinProd_eq
  {d : Nat}
  {laws : Nat -> ProbabilityMeasure (ConfigSpace (Site d))}
  {limit : ProbabilityMeasure (ConfigSpace (Site d))}
  {A : Finset (Site d)}
-- given
  (h : WeakConvergesTo laws limit) :
-- imply
  Tendsto (fun n => ∫ omega, spinProd A omega ∂(laws n : Measure (ConfigSpace (Site d)))) atTop (nhds (∫ omega, spinProd A omega ∂(limit : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierA.WeakConvergesTo.tendsto_integral_spinProd h A

/--
[tendsto_prod_localSpinFactors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinConformalReduction.lean)
-/
@[path]
private lemma tendsto_prod_localSpinFactors_eq
  [Fintype iota]
-- given
  (localFactor : Nat -> iota -> Real)
  (Phi : Complex -> Complex)
  (a : iota -> Complex)
  (hlocal : forall i, Tendsto (fun n => localFactor n i) atTop (nhds (norm (deriv Phi (a i)) ^ isingSpinScalingDimension))) :
-- imply
  Tendsto (fun n => ∏ i, localFactor n i) atTop (nhds (spinConformalFactor Phi a)) := by
-- proof
  apply StatMech.FrontierA.tendsto_prod_localSpinFactors localFactor Phi a hlocal

/--
[tendsto_spinCorrelation_mul_localFactors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinConformalReduction.lean)
-/
@[path]
private lemma tendsto_spinCorrelation_mul_localFactors_eq
  [Fintype iota]
  {limit : Real}
-- given
  (localFactor : Nat -> iota -> Real)
  (Phi : Complex -> Complex)
  (a : iota -> Complex)
  (correlation : Nat -> Real)
  (hlocal : forall i, Tendsto (fun n => localFactor n i) atTop (nhds (norm (deriv Phi (a i)) ^ isingSpinScalingDimension)))
  (hcorrelation : Tendsto correlation atTop (nhds limit)) :
-- imply
  Tendsto (fun n => (∏ i, localFactor n i) * correlation n) atTop (nhds (spinConformalFactor Phi a * limit)) := by
-- proof
  apply StatMech.FrontierA.tendsto_spinCorrelation_mul_localFactors localFactor Phi a correlation limit hlocal hcorrelation

/--
[tendsto_spinCorrelation_of_asymptotic_conformal_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinConformalReduction.lean)
-/
@[path]
private lemma tendsto_spinCorrelation_of_asymptotic_conformal_transport_eq
  [Fintype iota]
  {limit : Real}
-- given
  (localFactor : Nat -> iota -> Real)
  (Phi : Complex -> Complex)
  (a : iota -> Complex)
  (source target : Nat -> Real)
  (hlocal : forall i, Tendsto (fun n => localFactor n i) atTop (nhds (norm (deriv Phi (a i)) ^ isingSpinScalingDimension)))
  (hsource : Tendsto source atTop (nhds limit))
  (htransport : Tendsto (fun n => target n - (∏ i, localFactor n i) * source n) atTop (nhds 0)) :
-- imply
  Tendsto target atTop (nhds (spinConformalFactor Phi a * limit)) := by
-- proof
  apply StatMech.FrontierA.tendsto_spinCorrelation_of_asymptotic_conformal_transport localFactor Phi a source target limit hlocal hsource htransport


-- created on 2026-10-23
