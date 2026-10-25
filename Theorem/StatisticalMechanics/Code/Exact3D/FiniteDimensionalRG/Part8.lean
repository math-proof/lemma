/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Def.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part9


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplitting

theorem cone_step {n : ℕ} (H : FiniteHyperbolicSplitting n)
    {η : ℝ} (hη : 0 ≤ η) {x : State n} (hx : H.cone η x) :
    H.cone η (H.step x) :=
  H.stable.step_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal
    hη H.stable_dominated hx


theorem cone_iterate {n : ℕ} (H : FiniteHyperbolicSplitting n)
    {η : ℝ} (hη : 0 ≤ η) {x : State n} (hx : H.cone η x)
    (k : ℕ) :
    H.cone η (H.iterate k x) := by
  unfold cone
  rw [H.iterate_fst_eq k x, H.iterate_snd_eq k x]
  exact
    H.stable.iterate_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal
      hη H.stable_dominated hx k


theorem rgMap_iterate_eq {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (scale : BlockScale) (k : ℕ) (x : State n) :
    ((H.rgMap scale).map^[k]) x = H.iterate k x := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simpa [iterate, rgMap] using congrArg H.step ih


theorem rgMap_cone_iterate {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (scale : BlockScale) {η : ℝ} (hη : 0 ≤ η) {x : State n}
    (hx : H.cone η x) (k : ℕ) :
    H.cone η (((H.rgMap scale).map^[k]) x) := by
  rw [H.rgMap_iterate_eq scale k x]
  exact H.cone_iterate hη hx k


theorem tendsto_rgMap_stable_supNormVec_zero_of_l1StepConstant_lt_one
    {n : ℕ} (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (hS : H.stable.l1StepConstant < 1) (x : State n) :
    Filter.Tendsto
      (fun k : ℕ =>
        RatInterval.supNormVec ((((H.rgMap scale).map^[k]) x).2))
      Filter.atTop (nhds 0) := by
  refine Filter.Tendsto.congr' ?_
    (H.tendsto_iterate_stable_supNormVec_zero_of_l1StepConstant_lt_one hS x)
  exact Filter.Eventually.of_forall fun k => by
    exact congrArg (fun y : State n => RatInterval.supNormVec y.2)
      (H.rgMap_iterate_eq scale k x).symm


theorem certificate_cone_iterate {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) {η : ℝ} (hη : 0 ≤ η)
    {x : (H.certificate scale M).H.carrier} (hx : H.cone η x) (k : ℕ) :
    H.cone η ((((H.certificate scale M).R.map)^[k]) x) := by
  simpa [certificate] using H.rgMap_cone_iterate scale hη hx k


theorem tendsto_certificate_stable_supNormVec_zero_of_l1StepConstant_lt_one
    {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι)
    (hS : H.stable.l1StepConstant < 1)
    (x : (H.certificate scale M).H.carrier) :
    Filter.Tendsto
      (fun k : ℕ =>
        RatInterval.supNormVec ((((H.certificate scale M).R.map)^[k]) x).2)
      Filter.atTop (nhds 0) := by
  simpa [certificate] using
    H.tendsto_rgMap_stable_supNormVec_zero_of_l1StepConstant_lt_one
      scale hS x


theorem certificate_valid_of_bridge {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ)
    (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength) :
    (H.certificate scale M).Valid correlationLength :=
  (H.certificate scale M).valid_of_bridge correlationLength
    (H.certificate_finiteCaseChecks scale M)
    (H.certificate_tailBounds scale M)
    (H.certificate_fixedPointEnclosure scale M)
    (H.certificate_linearizationEnclosure scale M)
    (H.certificate_hyperbolicSplitting scale M)
    (H.certificate_orbitEntry scale M)
    hbridge


theorem certificate_rgToExponentBridge_of_hasCriticalNu
    {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (H.certificate scale M).predictedExponent) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  (H.certificate scale M).bridge_of_hasCriticalNu correlationLength hν


theorem certificate_valid_of_hasCriticalNu {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (H.certificate scale M).predictedExponent) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H.certificate_rgToExponentBridge_of_hasCriticalNu
      scale M correlationLength hν)


theorem certificate_hasCriticalNu_of_bridge {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ)
    (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_bridge scale M correlationLength hbridge).hasCriticalNu


end FiniteHyperbolicSplitting
end Exact3D
end StatMech
