import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianMomentDeterminacy
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[probabilityMeasure_eq_of_complexMoments_of_localExp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentDeterminacy.lean)
-/
@[path]
private lemma probabilityMeasure_eq_of_complexMoments_of_localExp_eq
  {mu nu : Measure Real}
  [IsProbabilityMeasure mu]
  [IsProbabilityMeasure nu]
-- given
  (hmu : (0 : Real) ∈ interior (integrableExpSet id mu))
  (hnu : (0 : Real) ∈ interior (integrableExpSet id nu))
  (hmoments : ∀ n : Nat, (∫ x, (x : Complex) ^ n ∂mu) = ∫ x, (x : Complex) ^ n ∂nu) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FrontierA.probabilityMeasure_eq_of_complexMoments_of_localExp mu nu hmu hnu hmoments

/--
[probabilityMeasure_eq_of_realMoments_of_localExp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentDeterminacy.lean)
-/
@[path]
private lemma probabilityMeasure_eq_of_realMoments_of_localExp_eq
  {mu nu : Measure Real}
  [IsProbabilityMeasure mu]
  [IsProbabilityMeasure nu]
-- given
  (hmu : (0 : Real) ∈ interior (integrableExpSet id mu))
  (hnu : (0 : Real) ∈ interior (integrableExpSet id nu))
  (hmoments : ∀ n : Nat, (∫ x, x ^ n ∂mu) = ∫ x, x ^ n ∂nu) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FrontierA.probabilityMeasure_eq_of_realMoments_of_localExp mu nu hmu hnu hmoments

/--
[ScalarWickMoments.moments_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentDeterminacy.lean)
-/
@[path]
private lemma moments_eq_eq
  {variance : Real}
  {moments moments' : Nat → Real}
-- given
  (h : ScalarWickMoments variance moments)
  (h' : ScalarWickMoments variance moments') :
-- imply
  moments = moments' := by
-- proof
  apply StatMech.FrontierA.ScalarWickMoments.moments_eq h h'

/--
[probabilityMeasure_eq_of_wickMoments_of_localExp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentDeterminacy.lean)
-/
@[path]
private lemma probabilityMeasure_eq_of_wickMoments_of_localExp_eq
  {mu nu : Measure Real}
  [IsProbabilityMeasure mu]
  [IsProbabilityMeasure nu]
  {variance : Real}
-- given
  (hmu : (0 : Real) ∈ interior (integrableExpSet id mu))
  (hnu : (0 : Real) ∈ interior (integrableExpSet id nu))
  (hmuWick : ScalarWickMoments variance (fun n => ∫ x, x ^ n ∂mu))
  (hnuWick : ScalarWickMoments variance (fun n => ∫ x, x ^ n ∂nu)) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FrontierA.probabilityMeasure_eq_of_wickMoments_of_localExp mu nu variance hmu hnu hmuWick hnuWick

/--
[probabilityMeasure_eq_of_all_projection_map_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentDeterminacy.lean)
-/
@[path]
private lemma probabilityMeasure_eq_of_all_projection_map_eq_eq
  [MeasurableSpace E]
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]
  [BorelSpace E]
  [SecondCountableTopology E]
  [CompleteSpace E]
  {mu nu : Measure E}
  [IsProbabilityMeasure mu]
  [IsProbabilityMeasure nu]
-- given
  (hprojection : ∀ t : E, mu.map (InnerProductSpace.toDualMap Real E t) = nu.map (InnerProductSpace.toDualMap Real E t)) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FrontierA.probabilityMeasure_eq_of_all_projection_map_eq mu nu hprojection

/--
[probabilityMeasure_eq_of_projectionMoments_of_localExp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentDeterminacy.lean)
-/
@[path]
private lemma probabilityMeasure_eq_of_projectionMoments_of_localExp_eq
  [MeasurableSpace E]
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]
  [BorelSpace E]
  [SecondCountableTopology E]
  [CompleteSpace E]
  {mu nu : Measure E}
  [IsProbabilityMeasure mu]
  [IsProbabilityMeasure nu]
-- given
  (hmu : ∀ t : E, (0 : Real) ∈ interior (integrableExpSet id (mu.map (InnerProductSpace.toDualMap Real E t))))
  (hnu : ∀ t : E, (0 : Real) ∈ interior (integrableExpSet id (nu.map (InnerProductSpace.toDualMap Real E t))))
  (hmoments : ∀ (t : E) (n : Nat), (∫ x, (x : Complex) ^ n ∂(mu.map (InnerProductSpace.toDualMap Real E t))) = ∫ x, (x : Complex) ^ n ∂(nu.map (InnerProductSpace.toDualMap Real E t))) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FrontierA.probabilityMeasure_eq_of_projectionMoments_of_localExp mu nu hmu hnu hmoments

/--
[probabilityMeasure_eq_of_projectionRealMoments_of_localExp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentDeterminacy.lean)
-/
@[path]
private lemma probabilityMeasure_eq_of_projectionRealMoments_of_localExp_eq
  [MeasurableSpace E]
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]
  [BorelSpace E]
  [SecondCountableTopology E]
  [CompleteSpace E]
  {mu nu : Measure E}
  [IsProbabilityMeasure mu]
  [IsProbabilityMeasure nu]
-- given
  (hmu : ∀ t : E, (0 : Real) ∈ interior (integrableExpSet id (mu.map (InnerProductSpace.toDualMap Real E t))))
  (hnu : ∀ t : E, (0 : Real) ∈ interior (integrableExpSet id (nu.map (InnerProductSpace.toDualMap Real E t))))
  (hmoments : ∀ (t : E) (n : Nat), (∫ x, x ^ n ∂(mu.map (InnerProductSpace.toDualMap Real E t))) = ∫ x, x ^ n ∂(nu.map (InnerProductSpace.toDualMap Real E t))) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FrontierA.probabilityMeasure_eq_of_projectionRealMoments_of_localExp mu nu hmu hnu hmoments

/--
[probabilityMeasure_eq_of_projectionWickMoments_of_localExp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentDeterminacy.lean)
-/
@[path]
private lemma probabilityMeasure_eq_of_projectionWickMoments_of_localExp_eq
  [MeasurableSpace E]
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]
  [BorelSpace E]
  [SecondCountableTopology E]
  [CompleteSpace E]
  {mu nu : Measure E}
  [IsProbabilityMeasure mu]
  [IsProbabilityMeasure nu]
  {variance : E → Real}
-- given
  (hmu : ∀ t : E, (0 : Real) ∈ interior (integrableExpSet id (mu.map (InnerProductSpace.toDualMap Real E t))))
  (hnu : ∀ t : E, (0 : Real) ∈ interior (integrableExpSet id (nu.map (InnerProductSpace.toDualMap Real E t))))
  (hmuWick : ∀ t : E, ScalarWickMoments (variance t) (fun n => ∫ x, x ^ n ∂(mu.map (InnerProductSpace.toDualMap Real E t))))
  (hnuWick : ∀ t : E, ScalarWickMoments (variance t) (fun n => ∫ x, x ^ n ∂(nu.map (InnerProductSpace.toDualMap Real E t)))) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FrontierA.probabilityMeasure_eq_of_projectionWickMoments_of_localExp mu nu variance hmu hnu hmuWick hnuWick


-- created on 2026-10-23
