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
import Def.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part8


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplitting

@[simp] theorem certificate_retarget {n : ℕ} {ι κ : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (N : CriticalModel κ) :
    H.certificate scale N = (H.certificate scale M).retarget N :=
  rfl

@[simp] theorem certificate_thermalEigenvalue_eq {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).thermalEigenvalue = H.thermal :=
  rfl

@[simp] theorem certificate_scale_eq {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).scale = scale :=
  rfl


theorem certificate_predictedExponent_eq {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).predictedExponent =
      predictedNu scale H.thermal :=
  rfl


theorem certificate_fixedPointEnclosure {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).FixedPointEnclosure :=
  H.step_origin

theorem certificate_finiteCaseChecks {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).FiniteCaseChecks :=
  trivial

theorem certificate_tailBounds {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).TailBounds :=
  trivial

theorem certificate_linearizationEnclosure {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).LinearizationEnclosure :=
  (H.certificate scale M).linearizationEnclosure_of_thermal_gt_one

theorem certificate_hyperbolicSplitting {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).HyperbolicSplitting :=
  (H.certificate scale M).hyperbolicSplitting_of_thermal_gt_one

theorem certificate_orbitEntry {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).OrbitEntry :=
  trivial


theorem iterate_fst_eq {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (k : ℕ) (x : State n) :
    (H.iterate k x).1 = H.thermal ^ k * x.1 := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simp [iterate, step, ih, pow_succ', mul_assoc]


theorem iterate_snd_eq {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (k : ℕ) (x : State n) :
    (H.iterate k x).2 = H.stable.iterate k x.2 := by
  induction k with
  | zero =>
      simp [iterate, StableBlockWithRemainder.iterate]
  | succ k ih =>
      simp [iterate, StableBlockWithRemainder.iterate, step, ih]


theorem tendsto_iterate_stable_supNormVec_zero_of_l1StepConstant_lt_one
    {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (hS : H.stable.l1StepConstant < 1) (x : State n) :
    Filter.Tendsto
      (fun k : ℕ => RatInterval.supNormVec (H.iterate k x).2)
      Filter.atTop (nhds 0) := by
  refine Filter.Tendsto.congr' ?_
    (H.stable.tendsto_iterate_supNormVec_zero_of_l1StepConstant_lt_one
      hS x.2)
  exact Filter.Eventually.of_forall fun k => by
    exact congrArg RatInterval.supNormVec (H.iterate_snd_eq k x).symm


end FiniteHyperbolicSplitting
end Exact3D
end StatMech
