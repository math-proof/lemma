import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianScalingLimit
open Filter MeasureTheory Topology StatMech StatMech.FrontierA


/--
[weakLimit_eq_of_positive_torusScaledSmeared_newmanFourth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianScalingLimit.lean)
-/
@[path]
private lemma weakLimit_eq_of_positive_torusScaledSmeared_newmanFourth_eq
  {d : Nat}
  {beta : Real}
  {c : Nat → Real}
  {a : (k : Nat) → IsingDyadicTorus d k → Real}
  {potential : (k : Nat) → IsingDyadicTorus d k → Real}
  {mu nu : ProbabilityMeasure Real}
  {variance : Real → Real}
  {energyBound : Real → Real}
-- given
  (hbeta : 0 < beta)
  (ha : ∀ k x, 0 < a k x)
  (hpotential : ∀ k (u : IsingDyadicTorus d k → Real), isingTorusDirichletBilinear u (potential k) = ∑ x, u x * a k x)
  (hlim : Tendsto (fun k => isingTorusFieldLaw d k beta (isingTorusScaledSmearedField (c k) (a k))) atTop (nhds mu))
  (hvariance : ∀ t, Tendsto (fun k => isingTorusScaledSmearedCumulant beta (c k) t (a k) 2) atTop (nhds (variance t)))
  (hfourth : ∀ t, Tendsto (fun k => isingTorusScaledSmearedCumulant beta (c k) t (a k) 4) atTop (nhds 0))
  (henergy : ∀ k t, isingTorusDirichlet ((t * c k) • potential k) ≤ energyBound t)
  (hnuExp : ∀ t : Real, (0 : Real) ∈ interior (integrableExpSet id ((nu : Measure Real).map (InnerProductSpace.toDualMap Real Real t))))
  (hnuWick : ∀ t : Real, ScalarWickMoments (variance t) (fun order => ∫ x, x ^ order ∂((nu : Measure Real).map (InnerProductSpace.toDualMap Real Real t)))) :
-- imply
  (mu : Measure Real) = (nu : Measure Real) := by
-- proof
  apply StatMech.FrontierA.weakLimit_eq_of_positive_torusScaledSmeared_newmanFourth d beta hbeta c a ha potential hpotential mu nu hlim variance hvariance hfourth energyBound henergy hnuExp hnuWick

/--
[tendsto_cumulant_of_tendsto_sub_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianScalingLimit.lean)
-/
@[path]
private lemma tendsto_cumulant_of_tendsto_sub_zero_eq
  {torus box : Nat → Real}
  {limit : Real}
-- given
  (hbox : Tendsto box atTop (nhds limit))
  (happrox : Tendsto (fun n => torus n - box n) atTop (nhds 0)) :
-- imply
  Tendsto torus atTop (nhds limit) := by
-- proof
  apply StatMech.FrontierA.tendsto_cumulant_of_tendsto_sub_zero torus box limit hbox happrox

/--
[weakLimit_eq_of_torus_freeBoxCumulantApproximation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianScalingLimit.lean)
-/
@[path]
private lemma weakLimit_eq_of_torus_freeBoxCumulantApproximation_eq
  [MeasurableSpace E]
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]
  [BorelSpace E]
  [SecondCountableTopology E]
  [CompleteSpace E]
  {d : Nat}
  {beta : Real}
  {X : (n : Nat) → ConfigSpace (IsingDyadicTorus d n) → E}
  {mu nu : ProbabilityMeasure E}
  {variance : E → Real}
  {torusCumulants boxCumulants : Nat → E → Nat → Real}
  {energyBound : E → Real}
-- given
  (hbeta : 0 < beta)
  (hlim : Tendsto (fun n => isingTorusFieldLaw d n beta (X n)) atTop (nhds mu))
  (hrecurrence : ∀ t : E, HasScalarMomentCumulantRecurrence (fun scale order => ∫ x, x ^ order ∂(((isingTorusFieldLaw d scale beta (X scale)).map (InnerProductSpace.toDualMap Real E t).continuous.measurable.aemeasurable : ProbabilityMeasure Real) : Measure Real)) (fun scale order => torusCumulants scale t order))
  (hboxVariance : ∀ t : E, Tendsto (fun n => boxCumulants n t 2) atTop (nhds (variance t)))
  (hboxNonGaussian : ∀ (t : E) (order : Nat), order ≠ 2 → Tendsto (fun n => boxCumulants n t order) atTop (nhds 0))
  (happrox : ∀ (t : E) (order : Nat), Tendsto (fun n => torusCumulants n t order - boxCumulants n t order) atTop (nhds 0))
  (f h : (n : Nat) → E → IsingDyadicTorus d n → Real)
  (hprojection : ∀ n t sigma, InnerProductSpace.toDualMap Real E t (X n sigma) = isingTorusSmearedSpin (f n t) sigma)
  (hpotential : ∀ n t u, isingTorusDirichletBilinear u (h n t) = ∑ x, u x * f n t x)
  (henergy : ∀ n t, isingTorusDirichlet (h n t) ≤ energyBound t)
  (hnuExp : ∀ t : E, (0 : Real) ∈ interior (integrableExpSet id ((nu : Measure E).map (InnerProductSpace.toDualMap Real E t))))
  (hnuWick : ∀ t : E, ScalarWickMoments (variance t) (fun order => ∫ x, x ^ order ∂((nu : Measure E).map (InnerProductSpace.toDualMap Real E t)))) :
-- imply
  (mu : Measure E) = (nu : Measure E) := by
-- proof
  apply StatMech.FrontierA.weakLimit_eq_of_torus_freeBoxCumulantApproximation d beta hbeta X mu nu hlim variance torusCumulants boxCumulants hrecurrence hboxVariance hboxNonGaussian happrox f h hprojection hpotential energyBound henergy hnuExp hnuWick


-- created on 2026-10-23
