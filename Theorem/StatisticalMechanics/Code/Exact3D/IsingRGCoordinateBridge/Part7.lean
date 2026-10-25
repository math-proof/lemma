/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Structure.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge.Part4


namespace StatMech

namespace Exact3D

namespace IsingMassRGCoordinateBridgeInputs

variable {C : RGCertificate Ising3DModel}


theorem mass_scaling
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.mass β =
      T.scaffold.massPrefactor β *
        Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) :=
  T.extractsMassScaling T.massCovariance T.coordinateCovariance
    T.stableManifoldControl T.microscopicOrbitEntry β hβ


theorem renormalizedBeta_mem_leftCriticalInterval
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.renormalizedBeta β ∈ T.scaffold.leftCriticalInterval :=
  T.scaffold.mass_covariance_maps_interval T.massCovariance hβ


theorem betaC_sub_renormalizedBeta_pos
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    0 < Ising.betaC 3 - T.scaffold.renormalizedBeta β :=
  T.scaffold.betaC_sub_pos_of_mem_leftCriticalInterval
    (T.renormalizedBeta_mem_leftCriticalInterval hβ)


theorem betaC_sub_renormalizedBeta_lt_delta
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    Ising.betaC 3 - T.scaffold.renormalizedBeta β < T.scaffold.δ :=
  T.scaffold.betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (T.renormalizedBeta_mem_leftCriticalInterval hβ)


theorem mass_covariance_lattice_scale
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.mass (T.scaffold.renormalizedBeta β) =
      T.scaffold.latticeRG.kernel.scale.toReal * T.scaffold.mass β :=
  T.scaffold.mass_covariance_lattice_scale T.massCovariance hβ


theorem mass_covariance_certificate_scale
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    T.scaffold.mass (T.scaffold.renormalizedBeta β) =
      C.scale.toReal * T.scaffold.mass β :=
  T.scaffold.mass_covariance_certificate_scale T.massCovariance hβ


theorem renormalizedBeta_iterate_mem_leftCriticalInterval
    (T : IsingMassRGCoordinateBridgeInputs C)
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


theorem mass_covariance_iterate_certificate_scale
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    ∀ k : ℕ,
      T.scaffold.mass ((T.scaffold.renormalizedBeta^[k]) β) =
        (C.scale.toReal ^ k) * T.scaffold.mass β := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hmem :
          (T.scaffold.renormalizedBeta^[k]) β ∈
            T.scaffold.leftCriticalInterval :=
        T.renormalizedBeta_iterate_mem_leftCriticalInterval hβ k
      have hstep := T.mass_covariance_certificate_scale hmem
      calc
        T.scaffold.mass
            ((T.scaffold.renormalizedBeta^[Nat.succ k]) β)
            =
            T.scaffold.mass
              (T.scaffold.renormalizedBeta
                ((T.scaffold.renormalizedBeta^[k]) β)) := by
          rw [Function.iterate_succ_apply']
        _ =
            C.scale.toReal *
              T.scaffold.mass
                ((T.scaffold.renormalizedBeta^[k]) β) :=
          hstep
        _ =
            C.scale.toReal *
              ((C.scale.toReal ^ k) * T.scaffold.mass β) := by
          rw [ih]
        _ =
            (C.scale.toReal ^ Nat.succ k) * T.scaffold.mass β := by
          rw [pow_succ]
          ring


theorem coordinate_rg_covariance_iterate
    (T : IsingMassRGCoordinateBridgeInputs C)
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
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    C.R.map (T.scaffold.coordinate β) =
      T.scaffold.coordinate (T.scaffold.renormalizedBeta β) :=
  T.scaffold.coordinate_rg_covariance T.coordinateCovariance hβ


theorem eventually_mem_leftCriticalInterval
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ T.scaffold.leftCriticalInterval :=
  T.scaffold.eventually_mem_leftCriticalInterval


theorem eventually_betaC_sub_pos
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  T.scaffold.eventually_betaC_sub_pos


theorem eventually_betaC_sub_lt_delta
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.scaffold.δ :=
  T.scaffold.eventually_betaC_sub_lt_delta


theorem eventually_coordinate_mem_rgNeighborhood
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.coordinate β ∈ T.scaffold.rgNeighborhood :=
  T.microscopicOrbitEntry


theorem eventually_renormalizedBeta_mem_leftCriticalInterval
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.renormalizedBeta β ∈ T.scaffold.leftCriticalInterval := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.renormalizedBeta_mem_leftCriticalInterval hβ


theorem eventually_betaC_sub_renormalizedBeta_pos
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - T.scaffold.renormalizedBeta β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.betaC_sub_renormalizedBeta_pos hβ


theorem eventually_betaC_sub_renormalizedBeta_lt_delta
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - T.scaffold.renormalizedBeta β < T.scaffold.δ := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.betaC_sub_renormalizedBeta_lt_delta hβ


theorem eventually_mass_covariance_lattice_scale
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.mass (T.scaffold.renormalizedBeta β) =
        T.scaffold.latticeRG.kernel.scale.toReal * T.scaffold.mass β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.mass_covariance_lattice_scale hβ


theorem eventually_mass_covariance_certificate_scale
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.mass (T.scaffold.renormalizedBeta β) =
        C.scale.toReal * T.scaffold.mass β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.mass_covariance_certificate_scale hβ


theorem eventually_mass_pos
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.scaffold.mass β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.mass_pos β hβ


theorem eventually_massPrefactor_pos
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.scaffold.massPrefactor β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.massPrefactor_pos β hβ


theorem eventually_mass_scaling
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.mass β =
        T.scaffold.massPrefactor β *
          Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.mass_scaling hβ


theorem eventually_correlationLength_eq_inv_mass
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.correlationLength β = (T.scaffold.mass β)⁻¹ := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.correlationLength_eq_inv_mass β hβ


theorem eventually_coordinate_rg_covariance
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      C.R.map (T.scaffold.coordinate β) =
        T.scaffold.coordinate (T.scaffold.renormalizedBeta β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.coordinate_rg_covariance hβ


theorem hasInverseCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay (T.scaffold.mass β) :=
  T.realizesInverseXAxisLength β hβ


theorem eventually_hasInverseCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (T.scaffold.mass β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasInverseCorrelationLength hβ


theorem hasCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C)
    {β : ℝ} (hβ : β ∈ T.scaffold.leftCriticalInterval) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.scaffold.correlationLength β) := by
  have hξ :
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.scaffold.mass β)⁻¹ :=
    (T.hasInverseCorrelationLength hβ).hasCorrelationLength_inv
      (T.mass_pos β hβ)
  simpa [T.correlationLength_eq_inv_mass β hβ] using hξ


theorem eventually_hasCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.scaffold.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ


end IsingMassRGCoordinateBridgeInputs
end Exact3D
end StatMech
