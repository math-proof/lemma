/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part136
import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentTheorem
import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BcEqIsing
import Theorem.StatisticalMechanics.Code.Ising.TransitionAssembly
import Abbrev.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part2


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem ising3D_eventual_positiveMagnetization_of_transition_regime
    (hregime : Ising3DTransitionRegime) :
    ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β := by
  obtain ⟨βc, _hβc, _hsub, hsuper⟩ := hregime
  exact ⟨βc, hsuper⟩

set_option linter.style.longLine false in

theorem tildeBetaCIsingSet_bddAbove_of_zero_on_set_and_transition_regime
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hregime : Ising3DTransitionRegime) :
    BddAbove (Sharpness.tildeBetaCIsingSet 3) :=
  tildeBetaCIsingSet_bddAbove_of_zero_on_set_and_eventual_pos
    hzeroSet
    (ising3D_eventual_positiveMagnetization_of_transition_regime hregime)

set_option linter.style.longLine false in


theorem ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_transition_regime
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hregime : Ising3DTransitionRegime) :
    0 < Sharpness.tildeBetaCIsing 3 :=
  ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_eventual_pos
    hzeroSet
    (ising3D_eventual_positiveMagnetization_of_transition_regime hregime)

set_option linter.style.longLine false in


theorem exists_tildeBetaCIsingSet_member_gt_of_lt_tildeBetaC
    {β : ℝ}
    (hβ : β < Sharpness.tildeBetaCIsing 3) :
    ∃ γ ∈ Sharpness.tildeBetaCIsingSet 3, β < γ := by
  unfold Sharpness.tildeBetaCIsing at hβ
  exact
    exists_lt_of_lt_csSup
      ⟨ising3DPositiveWitnessBeta,
        ising3D_tildeBetaCIsingSet_positive_singleton_mem⟩
      hβ

set_option linter.style.longLine false in


theorem ising3D_magnetization_monotone_of_volume_tendsto
    {volumeMag : ℕ → ℝ → ℝ}
    (hfiniteMono : ∀ N, Monotone (volumeMag N))
    (hfullLimit : ∀ β,
      Filter.Tendsto (fun N : ℕ => volumeMag N β) Filter.atTop
        (nhds (Ising.magnetization 3 β))) :
    Monotone (Ising.magnetization 3) := by
  intro β₁ β₂ hβ
  exact le_of_tendsto_of_tendsto (hfullLimit β₁) (hfullLimit β₂)
    (Filter.Eventually.of_forall fun N => hfiniteMono N hβ)

set_option linter.style.longLine false in


theorem ising3D_vanish_below_tildeBetaC_of_zero_on_set_monotone_nonneg
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hmono : Monotone (Ising.magnetization 3))
    (hnonneg : ∀ β, 0 ≤ Ising.magnetization 3 β) :
    ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0 := by
  intro β hβ
  obtain ⟨γ, hγ, hβγ⟩ :=
    exists_tildeBetaCIsingSet_member_gt_of_lt_tildeBetaC hβ
  have hle : Ising.magnetization 3 β ≤ 0 := by
    have hmono_le := hmono hβγ.le
    rw [hzeroSet γ hγ] at hmono_le
    exact hmono_le
  exact le_antisymm hle (hnonneg β)

set_option linter.style.longLine false in


theorem ising3D_vanish_below_tildeBetaC_of_zero_on_set_volumeMonotone_nonneg
    {volumeMag : ℕ → ℝ → ℝ}
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hfiniteMono : ∀ N, Monotone (volumeMag N))
    (hfullLimit : ∀ β,
      Filter.Tendsto (fun N : ℕ => volumeMag N β) Filter.atTop
        (nhds (Ising.magnetization 3 β)))
    (hnonneg : ∀ β, 0 ≤ Ising.magnetization 3 β) :
    ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0 :=
  ising3D_vanish_below_tildeBetaC_of_zero_on_set_monotone_nonneg
    hzeroSet
    (ising3D_magnetization_monotone_of_volume_tendsto
      hfiniteMono hfullLimit)
    hnonneg

set_option linter.style.longLine false in


theorem ising3D_not_positive_below_tildeBetaC_of_zero_on_set_monotone
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hmono : Monotone (Ising.magnetization 3)) :
    ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      ¬ 0 < Ising.magnetization 3 β := by
  intro β hβ hpos
  obtain ⟨γ, hγ, hβγ⟩ :=
    exists_tildeBetaCIsingSet_member_gt_of_lt_tildeBetaC hβ
  have hle : Ising.magnetization 3 β ≤ 0 := by
    have hmono_le := hmono hβγ.le
    rw [hzeroSet γ hγ] at hmono_le
    exact hmono_le
  linarith

set_option linter.style.longLine false in


theorem ising3D_not_positive_below_tildeBetaC_of_zero_on_set_volumeMonotone
    {volumeMag : ℕ → ℝ → ℝ}
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hfiniteMono : ∀ N, Monotone (volumeMag N))
    (hfullLimit : ∀ β,
      Filter.Tendsto (fun N : ℕ => volumeMag N β) Filter.atTop
        (nhds (Ising.magnetization 3 β))) :
    ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      ¬ 0 < Ising.magnetization 3 β :=
  ising3D_not_positive_below_tildeBetaC_of_zero_on_set_monotone
    hzeroSet
    (ising3D_magnetization_monotone_of_volume_tendsto
      hfiniteMono hfullLimit)

set_option linter.style.longLine false in


theorem ising3D_betaC_pos_of_sharpness_bc_eq_inputs
    (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
    (hbdd : BddBelow (Ising.positiveMagnetizationSet 3))
    (hne : (Ising.positiveMagnetizationSet 3).Nonempty)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0) :
    0 < Ising.betaC 3 := by
  have heq :
      Ising.betaC 3 = Sharpness.tildeBetaCIsing 3 :=
    Sharpness.bc_eq_ising_of_meanfield
      (d := 3) htc_pos hbdd hne hsqrt hzero
  rwa [heq]

set_option linter.style.longLine false in


theorem ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_hne
    (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
    (hbdd : BddBelow (Ising.positiveMagnetizationSet 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_bc_eq_inputs
    htc_pos hbdd
    (ising3D_positiveMagnetizationSet_nonempty_of_meanfield htc_pos hsqrt)
    hsqrt hzero

set_option linter.style.longLine false in


theorem ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions
    (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_hne
    htc_pos
    (ising3D_positiveMagnetizationSet_bddBelow_of_vanish_below_tildeBetaC
      hzero)
    hsqrt hzero

set_option linter.style.longLine false in


theorem ising3D_betaC_pos_of_sharpness_bc_eq_inputs_tilde_bddAbove
    (hbddTilde : BddAbove (Sharpness.tildeBetaCIsingSet 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions
    (ising3D_tildeBetaCIsing_pos_of_bddAbove hbddTilde)
    hsqrt hzero

set_option linter.style.longLine false in


theorem ising3D_betaC_pos_of_sharpness_bc_eq_inputs_phi_barrier
    {B : ℝ}
    (hbarrier : ∀ β, B < β →
      ∀ S : Finset (StatMech.Lattice.Site 3),
        StatMech.Percolation.origin 3 ∈ S →
          1 ≤ Sharpness.phiIsing 3 β S)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions
    (ising3D_tildeBetaCIsing_pos_of_phi_barrier hbarrier)
    hsqrt hzero

set_option linter.style.longLine false in


theorem ising3D_betaC_pos_of_sharpness_bc_eq_inputs_zeroSet_eventual_pos
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions
    (ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_eventual_pos
      hzeroSet heventual)
    hsqrt hzero

set_option linter.style.longLine false in


theorem ising3D_betaC_pos_of_sharpness_bc_eq_inputs_zeroSet_eventual_pos_monotone_nonneg
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β)
    (hmono : Monotone (Ising.magnetization 3))
    (hnonneg : ∀ β, 0 ≤ Ising.magnetization 3 β)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions
    (ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_eventual_pos
      hzeroSet heventual)
    hsqrt
    (ising3D_vanish_below_tildeBetaC_of_zero_on_set_monotone_nonneg
      hzeroSet hmono hnonneg)

set_option linter.style.longLine false in


theorem ising3D_betaC_pos_of_tilde_pos_meanfield_not_positive_below
    (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hnotpos : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      ¬ 0 < Ising.magnetization 3 β) :
    0 < Ising.betaC 3 := by
  have hne :
      (Ising.positiveMagnetizationSet 3).Nonempty :=
    ising3D_positiveMagnetizationSet_nonempty_of_meanfield htc_pos hsqrt
  have htilde_le : Sharpness.tildeBetaCIsing 3 ≤ Ising.betaC 3 := by
    unfold Ising.betaC
    refine le_csInf hne ?_
    intro β hβ
    rw [Ising.mem_positiveMagnetizationSet] at hβ
    by_contra hnotle
    rw [not_le] at hnotle
    exact hnotpos β hnotle hβ
  exact lt_of_lt_of_le htc_pos htilde_le

set_option linter.style.longLine false in


theorem ising3D_betaC_pos_of_sharpness_zeroSet_eventual_pos_monotone
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β)
    (hmono : Monotone (Ising.magnetization 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_tilde_pos_meanfield_not_positive_below
    (ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_eventual_pos
      hzeroSet heventual)
    hsqrt
    (ising3D_not_positive_below_tildeBetaC_of_zero_on_set_monotone
      hzeroSet hmono)

set_option linter.style.longLine false in


theorem ising3D_betaC_pos_of_sharpness_zeroSet_transition_regime_monotone
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hregime : Ising3DTransitionRegime)
    (hmono : Monotone (Ising.magnetization 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_zeroSet_eventual_pos_monotone
    hzeroSet
    (ising3D_eventual_positiveMagnetization_of_transition_regime hregime)
    hmono hsqrt

set_option linter.style.longLine false in


theorem ising3D_betaC_pos_of_sharpness_zeroSet_transitionAssembly_monotone
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hmono : Monotone (Ising.magnetization 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_sharpness_zeroSet_transition_regime_monotone
    hzeroSet htransition.transitionRegime hmono hsqrt

set_option linter.style.longLine false in


theorem ising3D_betaC_pos_of_transition_regime_nonpositive_beta
    (hregime : Ising3DTransitionRegime)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
    0 < Ising.betaC 3 := by
  obtain ⟨β0, hβ0, hsub, hsuper⟩ := hregime
  have hne : (Ising.positiveMagnetizationSet 3).Nonempty := by
    refine ⟨β0 + 1, ?_⟩
    rw [Ising.mem_positiveMagnetizationSet]
    exact hsuper (β0 + 1) (by linarith)
  have hβ0_le : β0 ≤ Ising.betaC 3 := by
    unfold Ising.betaC
    refine le_csInf hne ?_
    intro β hβ
    rw [Ising.mem_positiveMagnetizationSet] at hβ
    by_contra hnotle
    rw [not_le] at hnotle
    by_cases hβpos : 0 < β
    · have hz := hsub β hβpos hnotle
      rw [hz] at hβ
      exact lt_irrefl 0 hβ
    · exact hnonpos β (not_lt.mp hβpos) hβ
  exact lt_of_lt_of_le hβ0 hβ0_le

set_option linter.style.longLine false in


theorem ising3D_exists_betaC_eq_transition_threshold_of_transition_regime_nonpositive_beta
    (hregime : Ising3DTransitionRegime)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
    ∃ β0 : ℝ, 0 < β0 ∧ Ising.betaC 3 = β0 ∧
      (∀ β, 0 < β → β < β0 → Ising.magnetization 3 β = 0) ∧
      (∀ β, β0 < β → 0 < Ising.magnetization 3 β) := by
  obtain ⟨β0, hβ0, hsub, hsuper⟩ := hregime
  have hβ0_lower : ∀ β, β ∈ Ising.positiveMagnetizationSet 3 → β0 ≤ β := by
    intro β hβ
    rw [Ising.mem_positiveMagnetizationSet] at hβ
    by_contra hnotle
    rw [not_le] at hnotle
    by_cases hβpos : 0 < β
    · have hz := hsub β hβpos hnotle
      rw [hz] at hβ
      exact lt_irrefl 0 hβ
    · exact hnonpos β (not_lt.mp hβpos) hβ
  have hbdd : BddBelow (Ising.positiveMagnetizationSet 3) :=
    ⟨β0, hβ0_lower⟩
  have hle : β0 ≤ Ising.betaC 3 := by
    unfold Ising.betaC
    refine le_csInf ?_ ?_
    · exact ⟨β0 + 1, by
        rw [Ising.mem_positiveMagnetizationSet]
        exact hsuper (β0 + 1) (by linarith)⟩
    · intro β hβ
      exact hβ0_lower β hβ
  have hge : Ising.betaC 3 ≤ β0 := by
    unfold Ising.betaC
    refine le_of_forall_gt_imp_ge_of_dense ?_
    intro β hβ
    exact csInf_le hbdd (by
      rw [Ising.mem_positiveMagnetizationSet]
      exact hsuper β hβ)
  exact ⟨β0, hβ0, le_antisymm hge hle, hsub, hsuper⟩

set_option linter.style.longLine false in


theorem ising3D_exists_IsingFK_betaC_eq_transition_threshold_of_transition_regime
    (hregime : Ising3DTransitionRegime) :
    ∃ β0 : ℝ, 0 < β0 ∧
      IsingFK.betaC (Ising.magnetization 3) = β0 ∧
      (∀ β, 0 < β → β < β0 → Ising.magnetization 3 β = 0) ∧
      (∀ β, β0 < β → 0 < Ising.magnetization 3 β) := by
  obtain ⟨β0, hβ0, hsub, hsuper⟩ := hregime
  let S : Set ℝ := {β : ℝ | 0 < β ∧ Ising.magnetization 3 β = 0}
  have hupper : ∀ β, β ∈ S → β ≤ β0 := by
    intro β hβ
    by_contra hnotle
    rw [not_le] at hnotle
    have hpos := hsuper β hnotle
    rw [hβ.2] at hpos
    exact lt_irrefl 0 hpos
  have hbdd : BddAbove S := ⟨β0, hupper⟩
  have hne : S.Nonempty := by
    refine ⟨β0 / 2, ?_⟩
    exact ⟨by linarith, hsub (β0 / 2) (by linarith) (by linarith)⟩
  have hle : IsingFK.betaC (Ising.magnetization 3) ≤ β0 := by
    unfold IsingFK.betaC
    exact csSup_le hne hupper
  have hge : β0 ≤ IsingFK.betaC (Ising.magnetization 3) := by
    unfold IsingFK.betaC
    refine le_of_forall_lt_imp_le_of_dense ?_
    intro a ha
    by_cases ha0 : a ≤ 0
    · have hmem : β0 / 2 ∈ S :=
        ⟨by linarith, hsub (β0 / 2) (by linarith) (by linarith)⟩
      exact le_trans (by linarith) (le_csSup hbdd hmem)
    · have hapos : 0 < a := lt_of_not_ge ha0
      let c : ℝ := (a + β0) / 2
      have hcpos : 0 < c := by
        dsimp [c]
        linarith
      have hcβ0 : c < β0 := by
        dsimp [c]
        linarith
      have hac : a ≤ c := by
        dsimp [c]
        linarith
      have hmem : c ∈ S := ⟨hcpos, hsub c hcpos hcβ0⟩
      exact le_trans hac (le_csSup hbdd hmem)
  exact ⟨β0, hβ0, le_antisymm hle hge, hsub, hsuper⟩

set_option linter.style.longLine false in


theorem ising3D_betaC_eq_IsingFK_betaC_of_transition_regime_nonpositive_beta
    (hregime : Ising3DTransitionRegime)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
    Ising.betaC 3 = IsingFK.betaC (Ising.magnetization 3) := by
  obtain ⟨β0, hβ0, hsub, hsuper⟩ := hregime
  have hfull :
      ∃ γ : ℝ, 0 < γ ∧ Ising.betaC 3 = γ ∧
        (∀ β, 0 < β → β < γ → Ising.magnetization 3 β = 0) ∧
        (∀ β, γ < β → 0 < Ising.magnetization 3 β) :=
    ising3D_exists_betaC_eq_transition_threshold_of_transition_regime_nonpositive_beta
      ⟨β0, hβ0, hsub, hsuper⟩ hnonpos
  have hpositive :
      ∃ γ : ℝ, 0 < γ ∧ IsingFK.betaC (Ising.magnetization 3) = γ ∧
        (∀ β, 0 < β → β < γ → Ising.magnetization 3 β = 0) ∧
        (∀ β, γ < β → 0 < Ising.magnetization 3 β) :=
    ising3D_exists_IsingFK_betaC_eq_transition_threshold_of_transition_regime
      ⟨β0, hβ0, hsub, hsuper⟩
  obtain ⟨βfull, _hβfull, hfull_eq, hfull_sub, hfull_super⟩ := hfull
  obtain ⟨βpos, _hβpos, hpos_eq, hpos_sub, hpos_super⟩ := hpositive
  have hfull_le_pos : βfull ≤ βpos := by
    refine le_of_forall_lt_imp_le_of_dense ?_
    intro a ha
    by_cases ha0 : a ≤ 0
    · exact le_trans ha0 (le_of_lt _hβpos)
    · have hapos : 0 < a := lt_of_not_ge ha0
      by_contra hnotle
      rw [not_le] at hnotle
      have hz := hfull_sub a hapos ha
      have hp := hpos_super a hnotle
      rw [hz] at hp
      exact lt_irrefl 0 hp
  have hpos_le_full : βpos ≤ βfull := by
    refine le_of_forall_lt_imp_le_of_dense ?_
    intro a ha
    by_cases ha0 : a ≤ 0
    · exact le_trans ha0 (le_of_lt _hβfull)
    · have hapos : 0 < a := lt_of_not_ge ha0
      by_contra hnotle
      rw [not_le] at hnotle
      have hz := hpos_sub a hapos ha
      have hp := hfull_super a hnotle
      rw [hz] at hp
      exact lt_irrefl 0 hp
  rw [hfull_eq, hpos_eq, le_antisymm hfull_le_pos hpos_le_full]

set_option linter.style.longLine false in


theorem ising3D_exists_IsingFK_betaC_eq_transition_threshold_of_transitionAssembly
    (htransition : Ising3DTransitionAssemblyInputs) :
    ∃ β0 : ℝ, 0 < β0 ∧
      IsingFK.betaC (Ising.magnetization 3) = β0 ∧
      (∀ β, 0 < β → β < β0 → Ising.magnetization 3 β = 0) ∧
      (∀ β, β0 < β → 0 < Ising.magnetization 3 β) :=
  ising3D_exists_IsingFK_betaC_eq_transition_threshold_of_transition_regime
    htransition.transitionRegime

set_option linter.style.longLine false in


theorem ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
    Ising.betaC 3 = IsingFK.betaC (Ising.magnetization 3) :=
  ising3D_betaC_eq_IsingFK_betaC_of_transition_regime_nonpositive_beta
    htransition.transitionRegime hnonpos

set_option linter.style.longLine false in


theorem ising3D_exists_betaC_eq_transition_threshold_of_transitionAssembly_nonpositive_beta
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
    ∃ β0 : ℝ, 0 < β0 ∧ Ising.betaC 3 = β0 ∧
      (∀ β, 0 < β → β < β0 → Ising.magnetization 3 β = 0) ∧
      (∀ β, β0 < β → 0 < Ising.magnetization 3 β) :=
  ising3D_exists_betaC_eq_transition_threshold_of_transition_regime_nonpositive_beta
    htransition.transitionRegime hnonpos

set_option linter.style.longLine false in


theorem ising3D_betaC_pos_of_transitionAssembly_nonpositive_beta
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
    0 < Ising.betaC 3 :=
  ising3D_betaC_pos_of_transition_regime_nonpositive_beta
    htransition.transitionRegime hnonpos

end Exact3D
end StatMech
