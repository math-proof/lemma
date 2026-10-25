import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianMomentConvergence
open Filter MeasureTheory Set Topology ProbabilityTheory StatMech StatMech.FrontierA


/--
[clippedPower_eq_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentConvergence.lean)
-/
@[path]
private lemma clippedPower_eq_self_eq
  {order : Nat}
  {A x : Real}
-- given
  (hA : 0 <= A)
  (hx : |x ^ order| <= A) :
-- imply
  clippedPower order A x = x ^ order := by
-- proof
  apply StatMech.FrontierA.clippedPower_eq_self order hA hx

/--
[abs_sub_clippedPower_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentConvergence.lean)
-/
@[path]
private lemma abs_sub_clippedPower_le_eq
  {order : Nat}
  {A : Real}
  {x : Real}
-- given
  (hA : 0 <= A) :
-- imply
  |x ^ order - clippedPower order A x| <= |x| ^ order := by
-- proof
  apply StatMech.FrontierA.abs_sub_clippedPower_le order hA x

/--
[integral_exp_abs_le_of_weakLimit_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentConvergence.lean)
-/
@[path]
private lemma integral_exp_abs_le_of_weakLimit_uniform_eq
  {mu : ProbabilityMeasure Real}
  {a C : Real}
-- given
  (muN : Nat -> ProbabilityMeasure Real)
  (hlim : Tendsto muN atTop (nhds mu))
  (hint : forall n, Integrable (fun x : Real => Real.exp (a * |x|)) (muN n : Measure Real))
  (hbound : forall n, (∫ x, Real.exp (a * |x|) ∂(muN n : Measure Real)) <= C) :
-- imply
  (∫ x, Real.exp (a * |x|) ∂(mu : Measure Real)) <= C := by
-- proof
  apply StatMech.FrontierA.integral_exp_abs_le_of_weakLimit_uniform muN mu hlim a C hint hbound

/--
[zero_mem_interior_integrableExpSet_of_integrable_exp_abs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentConvergence.lean)
-/
@[path]
private lemma zero_mem_interior_integrableExpSet_of_integrable_exp_abs_eq
  {mu : Measure Real}
  {a : Real}
-- given
  (ha : 0 < a)
  (hint : Integrable (fun x : Real => Real.exp (a * |x|)) mu) :
-- imply
  (0 : Real) ∈ interior (integrableExpSet id mu) := by
-- proof
  apply StatMech.FrontierA.zero_mem_interior_integrableExpSet_of_integrable_exp_abs mu a ha hint

/--
[integral_pow_tendsto_of_weakLimit_uniform_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentConvergence.lean)
-/
@[path]
private lemma integral_pow_tendsto_of_weakLimit_uniform_exp_eq
  {mu : ProbabilityMeasure Real}
  {a C : Real}
  {order : Nat}
-- given
  (muN : Nat -> ProbabilityMeasure Real)
  (hlim : Tendsto muN atTop (nhds mu))
  (ha : 0 < a)
  (hint : forall n, Integrable (fun x : Real => Real.exp (a * |x|)) (muN n : Measure Real))
  (hbound : forall n, (∫ x, Real.exp (a * |x|) ∂(muN n : Measure Real)) <= C) :
-- imply
  Tendsto (fun n => ∫ x, x ^ order ∂(muN n : Measure Real)) atTop (nhds (∫ x, x ^ order ∂(mu : Measure Real))) := by
-- proof
  apply StatMech.FrontierA.integral_pow_tendsto_of_weakLimit_uniform_exp muN mu hlim a C ha hint hbound order

/--
[weakLimit_eq_of_projection_cumulant_limits_uniform_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentConvergence.lean)
-/
@[path]
private lemma weakLimit_eq_of_projection_cumulant_limits_uniform_exp_eq
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
  (hrecurrence : ∀ t : E, HasScalarMomentCumulantRecurrence (fun scale order => ∫ x, x ^ order ∂((muN scale : Measure E).map (InnerProductSpace.toDualMap Real E t))) (fun scale order => cumulants scale t order))
  (hcumulants : ∀ (t : E) (order : Nat), Tendsto (fun scale => cumulants scale t order) atTop (nhds (scalarGaussianCumulant (variance t) order)))
  (a C : E -> Real)
  (ha : ∀ t, 0 < a t)
  (hint : ∀ (t : E) (scale : Nat), Integrable (fun x : Real => Real.exp (a t * |x|)) ((muN scale : Measure E).map (InnerProductSpace.toDualMap Real E t)))
  (hbound : ∀ (t : E) (scale : Nat), (∫ x, Real.exp (a t * |x|) ∂((muN scale : Measure E).map (InnerProductSpace.toDualMap Real E t))) <= C t)
  (hnuExp : ∀ t : E, (0 : Real) ∈ interior (integrableExpSet id ((nu : Measure E).map (InnerProductSpace.toDualMap Real E t))))
  (hnuWick : ∀ t : E, ScalarWickMoments (variance t) (fun order => ∫ x, x ^ order ∂((nu : Measure E).map (InnerProductSpace.toDualMap Real E t)))) :
-- imply
  (mu : Measure E) = (nu : Measure E) := by
-- proof
  apply StatMech.FrontierA.weakLimit_eq_of_projection_cumulant_limits_uniform_exp muN mu nu hlim variance cumulants hrecurrence hcumulants a C ha hint hbound hnuExp hnuWick


-- created on 2026-10-23
