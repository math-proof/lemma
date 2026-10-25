import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianTorusScalingHandoff
open Filter MeasureTheory Topology StatMech StatMech.FrontierA


/--
[integral_exp_abs_projection_isingTorusFieldLaw_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusScalingHandoff.lean)
-/
@[path]
private lemma integral_exp_abs_projection_isingTorusFieldLaw_le_eq
  [MeasurableSpace E]
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]
  [BorelSpace E]
  {d k : Nat}
  {beta : Real}
  {t : E}
  {s : Real}
-- given
  (hbeta : 0 < beta)
  (X : ConfigSpace (IsingDyadicTorus d k) -> E)
  (f h : IsingDyadicTorus d k -> Real)
  (hprojection : forall sigma, InnerProductSpace.toDualMap Real E t (X sigma) = isingTorusSmearedSpin f sigma)
  (hpotential : forall u : IsingDyadicTorus d k -> Real, isingTorusDirichletBilinear u h = ∑ x, u x * f x) :
-- imply
  (∫ x, Real.exp (s * |x|) ∂(((isingTorusFieldLaw d k beta X).map (InnerProductSpace.toDualMap Real E t).continuous.measurable.aemeasurable) : Measure Real)) <= 2 * Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta)) := by
-- proof
  apply StatMech.FrontierA.integral_exp_abs_projection_isingTorusFieldLaw_le d k beta hbeta X t f h hprojection hpotential s

/--
[integrable_exp_abs_projection_isingTorusFieldLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusScalingHandoff.lean)
-/
@[path]
private lemma integrable_exp_abs_projection_isingTorusFieldLaw_eq
  [MeasurableSpace E]
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]
  [BorelSpace E]
  {d k : Nat}
  {beta s : Real}
  {t : E}
-- given
  (X : ConfigSpace (IsingDyadicTorus d k) -> E) :
-- imply
  Integrable (fun x : Real => Real.exp (s * |x|)) (((isingTorusFieldLaw d k beta X).map (InnerProductSpace.toDualMap Real E t).continuous.measurable.aemeasurable) : Measure Real) := by
-- proof
  apply StatMech.FrontierA.integrable_exp_abs_projection_isingTorusFieldLaw d k beta s X t

/--
[weakLimit_eq_of_torus_projection_newmanFourth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusScalingHandoff.lean)
-/
@[path]
private lemma weakLimit_eq_of_torus_projection_newmanFourth_eq
  [MeasurableSpace E]
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]
  [BorelSpace E]
  [SecondCountableTopology E]
  [CompleteSpace E]
  {d : Nat}
  {beta : Real}
  {mu nu : ProbabilityMeasure E}
-- given
  (hbeta : 0 < beta)
  (X : (n : Nat) -> ConfigSpace (IsingDyadicTorus d n) -> E)
  (hlim : Tendsto (fun n => isingTorusFieldLaw d n beta (X n)) atTop (nhds mu))
  (variance : E -> Real)
  (cumulants : Nat -> E -> Nat -> Real)
  (hrecurrence : forall t : E, HasScalarMomentCumulantRecurrence (fun scale order => ∫ x, x ^ order ∂(((isingTorusFieldLaw d scale beta (X scale)).map (InnerProductSpace.toDualMap Real E t).continuous.measurable.aemeasurable : ProbabilityMeasure Real) : Measure Real)) (fun scale order => cumulants scale t order))
  (hcontrol : forall t : E, NewmanFourthCumulantControl (fun scale order => cumulants scale t order))
  (hvariance : forall t : E, Tendsto (fun scale => cumulants scale t 2) atTop (nhds (variance t)))
  (hfourth : forall t : E, Tendsto (fun scale => cumulants scale t 4) atTop (nhds 0))
  (f h : (n : Nat) -> E -> IsingDyadicTorus d n -> Real)
  (hprojection : forall n t sigma, InnerProductSpace.toDualMap Real E t (X n sigma) = isingTorusSmearedSpin (f n t) sigma)
  (hpotential : forall n t u, isingTorusDirichletBilinear u (h n t) = ∑ x, u x * f n t x)
  (energyBound : E -> Real)
  (henergy : forall n t, isingTorusDirichlet (h n t) <= energyBound t)
  (hnuExp : forall t : E, (0 : Real) ∈ interior (integrableExpSet id ((nu : Measure E).map (InnerProductSpace.toDualMap Real E t))))
  (hnuWick : forall t : E, ScalarWickMoments (variance t) (fun order => ∫ x, x ^ order ∂((nu : Measure E).map (InnerProductSpace.toDualMap Real E t)))) :
-- imply
  (mu : Measure E) = (nu : Measure E) := by
-- proof
  apply StatMech.FrontierA.weakLimit_eq_of_torus_projection_newmanFourth d beta hbeta X mu nu hlim variance cumulants hrecurrence hcontrol hvariance hfourth f h hprojection hpotential energyBound henergy hnuExp hnuWick


-- created on 2026-10-23
