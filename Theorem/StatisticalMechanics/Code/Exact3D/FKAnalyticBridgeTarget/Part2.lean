/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Structure.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget


namespace StatMech

namespace Exact3D

namespace FKToIsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


theorem hasCorrelationLength
    (T : FKToIsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.isingCorrelationLength β) :=
  T.realizesXAxisLength β hβ


theorem eventually_mem_betaLeftCriticalInterval
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) :=
  eventually_mem_fkBetaLeftCriticalIoo T.δ_pos


theorem betaC_sub_pos_of_mem_betaLeftCriticalInterval
    (T : FKToIsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_fkBetaLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval
    (T : FKToIsingAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.δ :=
  betaC_sub_lt_delta_of_mem_fkBetaLeftCriticalIoo hβ


theorem eventually_betaC_sub_pos
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_fkBetaLeftCriticalIoo T.δ_pos


theorem eventually_betaC_sub_lt_delta
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.δ :=
  eventually_betaC_sub_lt_delta_fkBetaLeftCriticalIoo T.δ_pos


theorem eventually_hasCorrelationLength
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.isingCorrelationLength β) := by
  filter_upwards [T.eventually_mem_betaLeftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ


theorem eventually_ising_fk_length_agree
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.isingCorrelationLength β =
        T.fkCorrelationLength (IsingFK.pOfBeta β) :=
  T.ising_fk_length_agree


theorem hasCriticalNu_comp_pOfBeta
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu (ParameterModel (Ising.betaC 3))
      (fun β => T.fkCorrelationLength (IsingFK.pOfBeta β))
      C.predictedExponent :=
  FKReparameterization.hasCriticalNu_comp_pOfBeta T.fk_hasCriticalNu


theorem hasCriticalNu
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      C.predictedExponent := by
  have hcomp_param := T.hasCriticalNu_comp_pOfBeta
  have hcomp_ising :
      HasCriticalNu Ising3DModel
        (fun β => T.fkCorrelationLength (IsingFK.pOfBeta β))
        C.predictedExponent :=
    hcomp_param.congr_betaC (by rfl)
  exact hcomp_ising.congr_eventually T.ising_fk_length_agree


theorem rgToExponentBridge
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.isingCorrelationLength :=
  C.rgToExponentBridge_of_hasCriticalNu T.isingCorrelationLength
    T.hasCriticalNu


theorem eventually_isingCorrelationLength_eq_liminfCorrelationLength
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.isingCorrelationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay := by
  filter_upwards [T.eventually_hasCorrelationLength] with β hβ
  exact hβ.liminfCorrelationLength_eq.symm


theorem rgToExponentBridge_liminfCorrelationLength
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  RGCertificate.rgToExponentBridge_congr_eventually
    T.rgToExponentBridge
    ((T.eventually_isingCorrelationLength_eq_liminfCorrelationLength).mono
      fun _ hβ => hβ.symm)


theorem hasCriticalNu_liminfCorrelationLength
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.rgToExponentBridge_liminfCorrelationLength


theorem valid_of_checks
    (T : FKToIsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.isingCorrelationLength where
  finiteCaseChecks := hfinite
  tailBounds := htail
  fixedPointEnclosure := hfixed
  linearizationEnclosure := hlinear
  hyperbolicSplitting := hhyperbolic
  orbitEntry := horbit
  bridge := T.rgToExponentBridge


theorem valid_of_checks_liminfCorrelationLength
    (T : FKToIsingAnalyticRGToExponentTarget C)
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


end FKToIsingAnalyticRGToExponentTarget
end Exact3D
end StatMech
