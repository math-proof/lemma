import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[scalarFourthCumulant_tendsto_zero_of_renormalizedCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianNewmanBridge.lean)
-/
@[path]
private lemma scalarFourthCumulant_tendsto_zero_of_renormalizedCoupling_eq
  {normalizationLimit : Real}
-- given
  (fourthMoment variance normalization : Nat -> Real)
  (hnonzero : forall scale, normalization scale ≠ 0)
  (hcoupling : Tendsto (fun scale => renormalizedFourPointCoupling (fourthMoment scale) (variance scale) (normalization scale)) atTop (nhds 0))
  (hnormalization : Tendsto normalization atTop (nhds normalizationLimit)) :
-- imply
  Tendsto (fun scale => scalarFourthCumulant (fourthMoment scale) (variance scale)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.scalarFourthCumulant_tendsto_zero_of_renormalizedCoupling fourthMoment variance normalization normalizationLimit hnonzero hcoupling hnormalization

/--
[cumulantLimits_of_newmanFourthControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianNewmanBridge.lean)
-/
@[path]
private lemma cumulantLimits_of_newmanFourthControl_eq
  {variance : Real}
-- given
  (cumulants : Nat -> Nat -> Real)
  (hcontrol : NewmanFourthCumulantControl cumulants)
  (hvariance : Tendsto (fun scale => cumulants scale 2) atTop (nhds variance))
  (hfourth : Tendsto (fun scale => cumulants scale 4) atTop (nhds 0)) :
-- imply
  forall order, Tendsto (fun scale => cumulants scale order) atTop (nhds (scalarGaussianCumulant variance order)) := by
-- proof
  apply StatMech.FrontierA.cumulantLimits_of_newmanFourthControl cumulants variance hcontrol hvariance hfourth

/--
[scalarWickMoments_of_newmanFourthControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianNewmanBridge.lean)
-/
@[path]
private lemma scalarWickMoments_of_newmanFourthControl_eq
  {variance : Real}
-- given
  (moments cumulants : Nat -> Nat -> Real)
  (limitMoments : Nat -> Real)
  (hrecurrence : HasScalarMomentCumulantRecurrence moments cumulants)
  (hmoments : forall order, Tendsto (fun scale => moments scale order) atTop (nhds (limitMoments order)))
  (hcontrol : NewmanFourthCumulantControl cumulants)
  (hvariance : Tendsto (fun scale => cumulants scale 2) atTop (nhds variance))
  (hfourth : Tendsto (fun scale => cumulants scale 4) atTop (nhds 0)) :
-- imply
  ScalarWickMoments variance limitMoments := by
-- proof
  apply StatMech.FrontierA.scalarWickMoments_of_newmanFourthControl moments cumulants limitMoments variance hrecurrence hmoments hcontrol hvariance hfourth

/--
[weakLimit_eq_of_projection_newmanFourth_uniform_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianNewmanBridge.lean)
-/
@[path]
private lemma weakLimit_eq_of_projection_newmanFourth_uniform_exp_eq
  [MeasurableSpace E]
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]
  [BorelSpace E]
  [SecondCountableTopology E]
  [CompleteSpace E]
  {mu nu : ProbabilityMeasure E}
-- given
  (muN : Nat -> ProbabilityMeasure E)
  (hlim : Tendsto muN atTop (nhds mu))
  (variance : E -> Real)
  (cumulants : Nat -> E -> Nat -> Real)
  (hrecurrence : forall t : E, HasScalarMomentCumulantRecurrence (fun scale order => ∫ x, x ^ order ∂((muN scale : Measure E).map (InnerProductSpace.toDualMap Real E t))) (fun scale order => cumulants scale t order))
  (hcontrol : forall t : E, NewmanFourthCumulantControl (fun scale order => cumulants scale t order))
  (hvariance : forall t : E, Tendsto (fun scale => cumulants scale t 2) atTop (nhds (variance t)))
  (hfourth : forall t : E, Tendsto (fun scale => cumulants scale t 4) atTop (nhds 0))
  (a C : E -> Real)
  (ha : forall t, 0 < a t)
  (hint : forall (t : E) (scale : Nat), Integrable (fun x : Real => Real.exp (a t * |x|)) ((muN scale : Measure E).map (InnerProductSpace.toDualMap Real E t)))
  (hbound : forall (t : E) (scale : Nat), (∫ x, Real.exp (a t * |x|) ∂((muN scale : Measure E).map (InnerProductSpace.toDualMap Real E t))) <= C t)
  (hnuExp : forall t : E, (0 : Real) ∈ interior (integrableExpSet id ((nu : Measure E).map (InnerProductSpace.toDualMap Real E t))))
  (hnuWick : forall t : E, ScalarWickMoments (variance t) (fun order => ∫ x, x ^ order ∂((nu : Measure E).map (InnerProductSpace.toDualMap Real E t)))) :
-- imply
  (mu : Measure E) = (nu : Measure E) := by
-- proof
  apply StatMech.FrontierA.weakLimit_eq_of_projection_newmanFourth_uniform_exp muN mu nu hlim variance cumulants hrecurrence hcontrol hvariance hfourth a C ha hint hbound hnuExp hnuWick


-- created on 2026-10-23
