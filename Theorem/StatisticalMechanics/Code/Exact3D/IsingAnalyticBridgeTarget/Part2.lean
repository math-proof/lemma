/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
import Structure.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget


namespace StatMech

namespace Exact3D

namespace IsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


theorem hasCorrelationLength
    (T : IsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.correlationLength β) :=
  T.realizesXAxisLength β hβ


theorem eventually_mem_leftCriticalInterval
    (T : IsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) :=
  eventually_mem_isingLeftCriticalIoo T.δ_pos


theorem betaC_sub_pos_of_mem_leftCriticalInterval
    (T : IsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_isingLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (T : IsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.δ :=
  betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo hβ


theorem eventually_betaC_sub_pos
    (T : IsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_isingLeftCriticalIoo T.δ_pos


theorem eventually_betaC_sub_lt_delta
    (T : IsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.δ :=
  eventually_betaC_sub_lt_delta_isingLeftCriticalIoo T.δ_pos


theorem eventually_hasCorrelationLength
    (T : IsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ


theorem eventually_prefactor_pos
    (T : IsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.prefactor β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.prefactor_pos β hβ


theorem eventually_length_scaling
    (T : IsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        T.prefactor β *
          Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.length_scaling β hβ


theorem rgToExponentBridge
    (T : IsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.correlationLength := by
  refine C.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    T.correlationLength T.prefactor T.δ T.δ_pos ?_ ?_ ?_
  · intro β hβ
    exact T.prefactor_pos β (by simpa [Ising3DModel] using hβ)
  · simpa [Ising3DModel] using T.prefactor_log_negligible
  · intro β hβ
    exact T.length_scaling β (by simpa [Ising3DModel] using hβ)


theorem hasCriticalNu
    (T : IsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent :=
  T.rgToExponentBridge


theorem eventually_correlationLength_eq_liminfCorrelationLength
    (T : IsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay := by
  filter_upwards [T.eventually_hasCorrelationLength] with β hβ
  exact hβ.liminfCorrelationLength_eq.symm


theorem rgToExponentBridge_liminfCorrelationLength
    (T : IsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) := by
  exact
    RGCertificate.rgToExponentBridge_congr_eventually
      T.rgToExponentBridge
      ((T.eventually_correlationLength_eq_liminfCorrelationLength).mono
        fun _ hβ => hβ.symm)


theorem hasCriticalNu_liminfCorrelationLength
    (T : IsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.rgToExponentBridge_liminfCorrelationLength


theorem valid_of_checks
    (T : IsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.correlationLength where
  finiteCaseChecks := hfinite
  tailBounds := htail
  fixedPointEnclosure := hfixed
  linearizationEnclosure := hlinear
  hyperbolicSplitting := hhyperbolic
  orbitEntry := horbit
  bridge := T.rgToExponentBridge


theorem valid_of_checks_liminfCorrelationLength
    (T : IsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  C.valid_of_bridge
    (fun β : ℝ =>
      liminfCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay)
    hfinite htail hfixed hlinear hhyperbolic horbit
    T.rgToExponentBridge_liminfCorrelationLength


end IsingAnalyticRGToExponentTarget
end Exact3D
end StatMech
