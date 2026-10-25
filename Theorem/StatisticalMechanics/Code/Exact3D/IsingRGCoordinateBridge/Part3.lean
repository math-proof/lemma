/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Structure.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge.Part2


namespace StatMech

namespace Exact3D

namespace IsingRGCoordinateBridgeInputs

variable {C : RGCertificate Ising3DModel}


theorem length_scaling
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.correlationLength β =
      T.scaffold.prefactor β *
        Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) :=
  T.extractsLengthScaling T.lengthCovariance T.coordinateCovariance
    T.stableManifoldControl T.microscopicOrbitEntry β hβ


theorem renormalizedBeta_mem_leftCriticalInterval
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.renormalizedBeta β ∈ T.scaffold.leftCriticalInterval :=
  T.scaffold.length_covariance_maps_interval T.lengthCovariance hβ


theorem betaC_sub_renormalizedBeta_pos
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    0 < Ising.betaC 3 - T.scaffold.renormalizedBeta β :=
  T.scaffold.betaC_sub_pos_of_mem_leftCriticalInterval
    (T.renormalizedBeta_mem_leftCriticalInterval hβ)


theorem betaC_sub_renormalizedBeta_lt_delta
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    Ising.betaC 3 - T.scaffold.renormalizedBeta β < T.scaffold.δ :=
  T.scaffold.betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (T.renormalizedBeta_mem_leftCriticalInterval hβ)


theorem length_covariance_lattice_scale
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.correlationLength (T.scaffold.renormalizedBeta β) =
      T.scaffold.correlationLength β /
        T.scaffold.latticeRG.kernel.scale.toReal :=
  T.scaffold.length_covariance_lattice_scale T.lengthCovariance hβ


theorem length_covariance_certificate_scale
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.correlationLength (T.scaffold.renormalizedBeta β) =
      T.scaffold.correlationLength β / C.scale.toReal :=
  T.scaffold.length_covariance_certificate_scale T.lengthCovariance hβ


theorem renormalizedBeta_iterate_mem_leftCriticalInterval
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    ∀ k : ℕ,
      (T.scaffold.renormalizedBeta^[k]) β ∈
        T.scaffold.leftCriticalInterval := by
  intro k
  induction k with
  | zero =>
      simpa using hβ
  | succ k ih =>
      simpa [Function.iterate_succ_apply'] using
        T.renormalizedBeta_mem_leftCriticalInterval ih


theorem length_covariance_iterate_certificate_scale
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    ∀ k : ℕ,
      T.scaffold.correlationLength
          ((T.scaffold.renormalizedBeta^[k]) β) =
        T.scaffold.correlationLength β / (C.scale.toReal ^ k) := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hmem :
          (T.scaffold.renormalizedBeta^[k]) β ∈
            T.scaffold.leftCriticalInterval :=
        T.renormalizedBeta_iterate_mem_leftCriticalInterval hβ k
      have hstep := T.length_covariance_certificate_scale hmem
      calc
        T.scaffold.correlationLength
            ((T.scaffold.renormalizedBeta^[Nat.succ k]) β)
            =
            T.scaffold.correlationLength
              (T.scaffold.renormalizedBeta
                ((T.scaffold.renormalizedBeta^[k]) β)) := by
          rw [Function.iterate_succ_apply']
        _ =
            T.scaffold.correlationLength
              ((T.scaffold.renormalizedBeta^[k]) β) / C.scale.toReal :=
          hstep
        _ =
            (T.scaffold.correlationLength β / (C.scale.toReal ^ k)) /
              C.scale.toReal := by
          rw [ih]
        _ =
            T.scaffold.correlationLength β /
              (C.scale.toReal ^ Nat.succ k) := by
          simp [pow_succ, div_div]


theorem coordinate_rg_covariance_iterate
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    ∀ k : ℕ,
      ((C.R.map)^[k]) (T.scaffold.coordinate β) =
        T.scaffold.coordinate ((T.scaffold.renormalizedBeta^[k]) β) := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hmem :
          (T.scaffold.renormalizedBeta^[k]) β ∈
            T.scaffold.leftCriticalInterval :=
        T.renormalizedBeta_iterate_mem_leftCriticalInterval hβ k
      calc
        ((C.R.map)^[Nat.succ k]) (T.scaffold.coordinate β)
            =
            C.R.map (((C.R.map)^[k]) (T.scaffold.coordinate β)) := by
          rw [Function.iterate_succ_apply']
        _ =
            C.R.map
              (T.scaffold.coordinate
                ((T.scaffold.renormalizedBeta^[k]) β)) := by
          rw [ih]
        _ =
            T.scaffold.coordinate
              (T.scaffold.renormalizedBeta
                ((T.scaffold.renormalizedBeta^[k]) β)) :=
          T.scaffold.coordinate_rg_covariance T.coordinateCovariance hmem
        _ =
            T.scaffold.coordinate
              ((T.scaffold.renormalizedBeta^[Nat.succ k]) β) := by
          rw [Function.iterate_succ_apply']


theorem coordinate_rg_covariance
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    C.R.map (T.scaffold.coordinate β) =
      T.scaffold.coordinate (T.scaffold.renormalizedBeta β) :=
  T.scaffold.coordinate_rg_covariance T.coordinateCovariance hβ


theorem eventually_mem_leftCriticalInterval
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ T.scaffold.leftCriticalInterval :=
  T.scaffold.eventually_mem_leftCriticalInterval


theorem eventually_betaC_sub_pos
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  T.scaffold.eventually_betaC_sub_pos


theorem eventually_betaC_sub_lt_delta
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.scaffold.δ :=
  T.scaffold.eventually_betaC_sub_lt_delta


theorem eventually_coordinate_mem_rgNeighborhood
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.coordinate β ∈ T.scaffold.rgNeighborhood :=
  T.microscopicOrbitEntry


theorem eventually_renormalizedBeta_mem_leftCriticalInterval
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.renormalizedBeta β ∈ T.scaffold.leftCriticalInterval := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.renormalizedBeta_mem_leftCriticalInterval hβ


theorem eventually_betaC_sub_renormalizedBeta_pos
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - T.scaffold.renormalizedBeta β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.betaC_sub_renormalizedBeta_pos hβ


theorem eventually_betaC_sub_renormalizedBeta_lt_delta
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - T.scaffold.renormalizedBeta β < T.scaffold.δ := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.betaC_sub_renormalizedBeta_lt_delta hβ


theorem eventually_length_covariance_lattice_scale
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.correlationLength (T.scaffold.renormalizedBeta β) =
        T.scaffold.correlationLength β /
          T.scaffold.latticeRG.kernel.scale.toReal := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.length_covariance_lattice_scale hβ


theorem eventually_length_covariance_certificate_scale
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.correlationLength (T.scaffold.renormalizedBeta β) =
        T.scaffold.correlationLength β / C.scale.toReal := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.length_covariance_certificate_scale hβ


theorem eventually_prefactor_pos
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.scaffold.prefactor β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.prefactor_pos β hβ


theorem eventually_length_scaling
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.correlationLength β =
        T.scaffold.prefactor β *
          Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.length_scaling hβ


theorem eventually_coordinate_rg_covariance
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      C.R.map (T.scaffold.coordinate β) =
        T.scaffold.coordinate (T.scaffold.renormalizedBeta β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.coordinate_rg_covariance hβ


theorem hasCorrelationLength
    (T : IsingRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.scaffold.correlationLength β) :=
  T.realizesXAxisLength β hβ


theorem eventually_hasCorrelationLength
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.scaffold.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ


end IsingRGCoordinateBridgeInputs
end Exact3D
end StatMech
