import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxSpinLimit
open MeasureTheory Filter Topology StatMech StatMech.FrontierB


/--
[isingExpectation_boxSpinSupport_mono_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxSpinLimit.lean)
-/
@[path]
private lemma isingExpectation_boxSpinSupport_mono_field_eq
  {d : ℕ}
  {n m : ℕ}
  {A : Finset (Site d)}
-- given
  (hnm : n ≤ m)
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hA : ↑A ⊆ box d n) :
-- imply
  isingExpectation (sctBoxGraph d n) beta h (spinProd (boxSpinSupport d n A)) ≤ isingExpectation (sctBoxGraph d m) beta h (spinProd (boxSpinSupport d m A)) := by
-- proof
  apply StatMech.FrontierB.isingExpectation_boxSpinSupport_mono_field d hnm beta h hbeta hh A hA

/--
[integral_freeMeasure_spinProd_tendsto_freeState_of_nonneg_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxSpinLimit.lean)
-/
@[path]
private lemma integral_freeMeasure_spinProd_tendsto_freeState_of_nonneg_field_eq
  {d : ℕ}
  {A : Finset (Site d)}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  Tendsto (fun n => ∫ omega, spinProd A omega ∂(freeMeasure d n beta h : Measure (ConfigSpace (Site d)))) atTop (nhds (∫ omega, spinProd A omega ∂(freeState d beta h : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierB.integral_freeMeasure_spinProd_tendsto_freeState_of_nonneg_field d beta h hbeta hh A


-- created on 2026-10-23
