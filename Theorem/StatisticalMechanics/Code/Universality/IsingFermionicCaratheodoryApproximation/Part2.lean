/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicScalingReduction
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part2
open Filter Set Topology Metric


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


variable (I : A.HolderInterpolation)


theorem exists_normalizedObservable_near
    (n : Nat) (z : Complex) (hz : z ∈ A.carrier n) :
    ∃ e : A.M n,
      dist (A.normalizedInterpolant n z)
          (@FKIsingDobrushinDomain.normalizedFermionicObservable
            (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e) ≤
        I.constant * A.mesh n ^ (I.exponent : Real) := by
  obtain ⟨e, he⟩ := A.carrier_near_medial n z hz
  refine ⟨e, ?_⟩
  rw [← A.normalizedInterpolant_medial n e]
  exact (I.holder n).dist_le_of_le hz (A.medial_mem_carrier n e) he


theorem holderInterpolation_error_tendsto_zero :
    Tendsto (fun n ↦ (I.constant : Real) *
      A.mesh n ^ (I.exponent : Real)) atTop (nhds 0) := by
  simpa using (tendsto_const_nhds.mul
    (A.mesh_tendsto_zero.rpow_const_nhds_zero I.exponent_pos) :
      Tendsto (fun n ↦ (I.constant : Real) *
        A.mesh n ^ (I.exponent : Real)) atTop (nhds ((I.constant : Real) * 0)))


theorem compact_norm_bound_finite_prefix
    (F : Nat → Complex → Complex) (K : Set Complex) (hK : IsCompact K)
    (hF : ∀ n, ContinuousOn (F n) K) (N : Nat) :
    ∃ C : Real, ∀ n < N, ∀ z ∈ K, ‖F n z‖ ≤ C := by
  induction N with
  | zero =>
      exact ⟨0, by omega⟩
  | succ N ih =>
      obtain ⟨C, hC⟩ := ih
      obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hF N)
      refine ⟨max C D, ?_⟩
      intro n hn z hz
      by_cases hnN : n = N
      · subst n
        exact (hD z hz).trans (le_max_right C D)
      · exact (hC n (by omega) z hz).trans (le_max_left C D)


theorem compactBounds_of_holderInterpolation_and_eventualMedialBounds
    (I : A.HolderInterpolation)
    (hhol : ∀ n, DifferentiableOn Complex (A.normalizedInterpolant n) A.U)
    (hmedial : ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
      ∃ B : Real, ∀ᶠ n in atTop, ∀ e : A.M n,
          (∃ z ∈ K, dist z (A.medialEmbedding n e) ≤ A.mesh n) →
          ‖@FKIsingDobrushinDomain.normalizedFermionicObservable
            (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e‖ ≤ B) :
    ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
      ∃ C : Real, ∀ n z, z ∈ K → ‖A.normalizedInterpolant n z‖ ≤ C := by
  intro K hK hKU
  obtain ⟨B, hB⟩ := hmedial K hK hKU
  have hcarrier := A.compact_eventually_mem K hK hKU
  have herror : ∀ᶠ n in atTop,
      (I.constant : Real) * A.mesh n ^ (I.exponent : Real) < 1 :=
    holderInterpolation_error_tendsto_zero A I
      (Iio_mem_nhds (by norm_num : (0 : Real) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hcarrier.and (herror.and hB))
  obtain ⟨C₀, hC₀⟩ := compact_norm_bound_finite_prefix
    A.normalizedInterpolant K hK
      (fun n ↦ (hhol n).continuousOn.mono hKU) N
  refine ⟨max C₀ (B + 1), ?_⟩
  intro n z hz
  by_cases hn : n < N
  · exact (hC₀ n hn z hz).trans (le_max_left C₀ (B + 1))
  · have htail := hN n (Nat.le_of_not_gt hn)
    have hzcarrier : z ∈ A.carrier n := htail.1 hz
    obtain ⟨e, he⟩ := A.carrier_near_medial n z hzcarrier
    have hobs := htail.2.2 e ⟨z, hz, he⟩
    have hnear :
        dist (A.normalizedInterpolant n z)
          (@FKIsingDobrushinDomain.normalizedFermionicObservable
            (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e) ≤
          I.constant * A.mesh n ^ (I.exponent : Real) := by
      rw [← A.normalizedInterpolant_medial n e]
      exact (I.holder n).dist_le_of_le hzcarrier
        (A.medial_mem_carrier n e) he
    calc
      ‖A.normalizedInterpolant n z‖ ≤
          ‖@FKIsingDobrushinDomain.normalizedFermionicObservable
            (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e‖ +
            ‖A.normalizedInterpolant n z -
              @FKIsingDobrushinDomain.normalizedFermionicObservable
                (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e‖ :=
        norm_le_norm_add_norm_sub' _ _
      _ ≤ B + (I.constant : Real) * A.mesh n ^ (I.exponent : Real) := by
        rw [← dist_eq_norm]
        exact add_le_add hobs hnear
      _ ≤ B + 1 := add_le_add (le_refl B) htail.2.1.le
      _ ≤ max C₀ (B + 1) := le_max_right C₀ (B + 1)


theorem compactBounds_of_holderInterpolation_and_medialBounds
    (I : A.HolderInterpolation)
    (hhol : ∀ n, DifferentiableOn Complex (A.normalizedInterpolant n) A.U)
    (hmedial : ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
      ∃ B : Real, ∀ n (e : A.M n),
        (∃ z ∈ K, dist z (A.medialEmbedding n e) ≤ A.mesh n) →
        ‖@FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e‖ ≤ B) :
    ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
      ∃ C : Real, ∀ n z, z ∈ K → ‖A.normalizedInterpolant n z‖ ≤ C := by
  apply compactBounds_of_holderInterpolation_and_eventualMedialBounds A I hhol
  intro K hK hKU
  obtain ⟨B, hB⟩ := hmedial K hK hKU
  exact ⟨B, Filter.Eventually.of_forall hB⟩


theorem scalingLimit_of_holderMedialBounds_and_primitiveIm
    (I : A.HolderInterpolation) (target Phi : Complex → Complex)
    (hhol : ∀ n, DifferentiableOn Complex (A.normalizedInterpolant n) A.U)
    (htarget : DifferentiableOn Complex target A.U)
    (htarget_ne : target A.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi A.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) A.U)
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (hmedial : ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
      ∃ B : Real, ∀ n (e : A.M n),
        (∃ z ∈ K, dist z (A.medialEmbedding n e) ≤ A.mesh n) →
        ‖@FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e‖ ≤ B)
    (hidentifyPrimitive : ∀ (phi psi : Nat → Nat) (f : Complex → Complex),
      StrictMono phi → StrictMono psi →
      TendstoLocallyUniformlyOn
        (fun n ↦ A.normalizedInterpolant (phi (psi n))) f atTop A.U →
      ∃ (P : Complex → Complex) (C : Real),
        DifferentiableOn Complex P A.U ∧
        Set.EqOn (deriv P) (fun z ↦ f z ^ 2) A.U ∧
        (∀ z ∈ A.U, (P z).im = (Phi z).im + C) ∧
        f A.root = target A.root) :
    TendstoLocallyUniformlyOn A.normalizedInterpolant target atTop A.U ∧
      TendstoLocallyUniformlyOn (deriv ∘ A.normalizedInterpolant)
        (deriv target) atTop A.U := by
  apply isingFermionic_scalingLimit_of_compactBounds_and_primitiveIm
    A.mesh A.rawInterpolant target Phi A.U A.root A.isOpen A.isPreconnected
    A.root_mem hhol htarget htarget_ne hPhi hPhideriv E
  · exact compactBounds_of_holderInterpolation_and_medialBounds
      A I hhol hmedial
  · exact hidentifyPrimitive


end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
