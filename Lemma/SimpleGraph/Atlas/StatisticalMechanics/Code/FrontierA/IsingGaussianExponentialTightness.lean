import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianExponentialTightness
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[truncatedExpAbs_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianExponentialTightness.lean)
-/
@[path]
private lemma truncatedExpAbs_nonneg_eq
  {a : Real}
  {n : Nat}
  {x : Real} :
-- imply
  0 <= truncatedExpAbs a n x := by
-- proof
  apply StatMech.FrontierA.truncatedExpAbs_nonneg a n x

/--
[truncatedExpAbs_le_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianExponentialTightness.lean)
-/
@[path]
private lemma truncatedExpAbs_le_exp_eq
  {a : Real}
  {n : Nat}
  {x : Real} :
-- imply
  truncatedExpAbs a n x <= Real.exp (a * |x|) := by
-- proof
  apply StatMech.FrontierA.truncatedExpAbs_le_exp a n x

/--
[truncatedExpAbs_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianExponentialTightness.lean)
-/
@[path]
private lemma truncatedExpAbs_mono_eq
  {a : Real} :
-- imply
  Monotone (fun n : Nat => (truncatedExpAbs a n : Real -> Real)) := by
-- proof
  apply StatMech.FrontierA.truncatedExpAbs_mono a

/--
[iSup_ofReal_truncatedExpAbs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianExponentialTightness.lean)
-/
@[path]
private lemma iSup_ofReal_truncatedExpAbs_eq
  {a x : Real} :
-- imply
  (⨆ n : Nat, ENNReal.ofReal (truncatedExpAbs a n x)) = ENNReal.ofReal (Real.exp (a * |x|)) := by
-- proof
  apply StatMech.FrontierA.iSup_ofReal_truncatedExpAbs a x

/--
[integrable_exp_abs_of_weakLimit_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianExponentialTightness.lean)
-/
@[path]
private lemma integrable_exp_abs_of_weakLimit_uniform_eq
  {mu : ProbabilityMeasure Real}
  {a C : Real}
-- given
  (muN : Nat -> ProbabilityMeasure Real)
  (hlim : Tendsto muN atTop (nhds mu))
  (hint : forall n, Integrable (fun x : Real => Real.exp (a * |x|)) (muN n : Measure Real))
  (hbound : forall n, (∫ x, Real.exp (a * |x|) ∂(muN n : Measure Real)) <= C) :
-- imply
  Integrable (fun x : Real => Real.exp (a * |x|)) (mu : Measure Real) := by
-- proof
  apply StatMech.FrontierA.integrable_exp_abs_of_weakLimit_uniform muN mu hlim a C hint hbound

/--
[zero_mem_interior_integrableExpSet_of_weakLimit_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianExponentialTightness.lean)
-/
@[path]
private lemma zero_mem_interior_integrableExpSet_of_weakLimit_uniform_eq
  {mu : ProbabilityMeasure Real}
  {a C : Real}
-- given
  (muN : Nat -> ProbabilityMeasure Real)
  (hlim : Tendsto muN atTop (nhds mu))
  (ha : 0 < a)
  (hint : forall n, Integrable (fun x : Real => Real.exp (a * |x|)) (muN n : Measure Real))
  (hbound : forall n, (∫ x, Real.exp (a * |x|) ∂(muN n : Measure Real)) <= C) :
-- imply
  (0 : Real) ∈ interior (integrableExpSet id (mu : Measure Real)) := by
-- proof
  apply StatMech.FrontierA.zero_mem_interior_integrableExpSet_of_weakLimit_uniform muN mu hlim a C ha hint hbound


-- created on 2026-10-23
