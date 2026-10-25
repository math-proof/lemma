/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

theorem fkRectCriticalClosedMass_cut_pos
    (R : FKRectTorus) {q : Real} (hq : 1 <= q) :
    0 < fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) := by
  have hlower := fkRectCritical_cutClosedMass_lower R hq
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos
      (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
      (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq
  exact (pow_pos hc _).trans_le hlower

theorem closedMass_mul_fkRectCriticalCutFreeEventMass
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (A : Set R.Configuration) :
    fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) *
        fkRectCriticalCutFreeEventMass R q A =
      fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} := by
  unfold fkRectCriticalCutFreeEventMass
  field_simp [ne_of_gt (fkRectCriticalClosedMass_cut_pos R hq)]

theorem fkRectCriticalCutFreeEventMass_univ
    (R : FKRectTorus) {q : Real} (hq : 1 <= q) :
    fkRectCriticalCutFreeEventMass R q Set.univ = 1 := by
  unfold fkRectCriticalCutFreeEventMass
  rw [show {eta : R.Configuration |
      FKRectCutClosedConfiguration R eta ∧ eta ∈ Set.univ} =
      {eta | FKRectCutClosedConfiguration R eta} by ext; simp]
  rw [fkRectCriticalEventMass_cutClosed_eq_closedMass]
  exact div_self (ne_of_gt (fkRectCriticalClosedMass_cut_pos R hq))


theorem fkRectGraphCriticalEventMass_eq_indexed_preimage
    (R : FKRectTorus) (q : Real)
    (B : Set (FKRectGraphConfiguration R)) :
    fkRectGraphCriticalEventMass R q B =
      fkRectCriticalEventMass R q
        (fkRectConfigurationGraphEquiv R ⁻¹' B) := by
  unfold fkRectGraphCriticalEventMass fkRectCriticalEventMass
  symm
  apply Fintype.sum_equiv (fkRectConfigurationGraphEquiv R)
  intro omega
  by_cases hB : fkRectConfigurationGraphEquiv R omega ∈ B
  · have hpre : omega ∈ fkRectConfigurationGraphEquiv R ⁻¹' B := hB
    rw [Set.indicator_of_mem hpre,
      Set.indicator_of_mem hB]
    exact (fkRectGraphCriticalRandomClusterProb_configurationGraphEquiv
      R q omega).symm
  · have hpre : omega ∉ fkRectConfigurationGraphEquiv R ⁻¹' B := hB
    rw [Set.indicator_of_notMem hpre,
      Set.indicator_of_notMem hB]


theorem fkRectCritical_cFE_pow_mul_forceEdgesClosed_preimage_le_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex) (A : Set R.Configuration) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalEventMass R q
          (fkRectForceEdgesClosed R I ⁻¹' A) ≤
      fkRectCriticalEventMass R q A := by
  let J := fkRectGraphEdgesOfIndices R I
  let B : Set (FKRectGraphConfiguration R) :=
    (fkRectConfigurationGraphEquiv R).symm ⁻¹' A
  have hpush :=
    fkRectGraphCritical_cFE_pow_mul_forceClosed_preimage_le_event
      R hq J B
  rw [show J.card = I.card by simp [J]] at hpush
  rw [fkRectGraphCriticalEventMass_eq_indexed_preimage,
    fkRectGraphCriticalEventMass_eq_indexed_preimage] at hpush
  have hright : fkRectConfigurationGraphEquiv R ⁻¹' B = A := by
    ext omega
    simp [B]
  have hleft : fkRectConfigurationGraphEquiv R ⁻¹'
        (fkRectGraphForceClosed R J ⁻¹' B) =
      fkRectForceEdgesClosed R I ⁻¹' A := by
    ext omega
    simp only [Set.mem_preimage]
    rw [← fkRectConfigurationGraphEquiv_forceEdgesClosed R I omega]
    simp [B]
  rwa [hleft, hright] at hpush


theorem fkRectCritical_cFE_pow_mul_forceEdgesOpen_preimage_le_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex) (A : Set R.Configuration) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalEventMass R q
          (fkRectForceEdgesOpen R I ⁻¹' A) ≤
      fkRectCriticalEventMass R q A := by
  let J := fkRectGraphEdgesOfIndices R I
  let B : Set (FKRectGraphConfiguration R) :=
    (fkRectConfigurationGraphEquiv R).symm ⁻¹' A
  have hpush :=
    fkRectGraphCritical_cFE_pow_mul_forceOpen_preimage_le_event
      R hq J B
  rw [show J.card = I.card by simp [J]] at hpush
  rw [fkRectGraphCriticalEventMass_eq_indexed_preimage,
    fkRectGraphCriticalEventMass_eq_indexed_preimage] at hpush
  have hright : fkRectConfigurationGraphEquiv R ⁻¹' B = A := by
    ext omega
    simp [B]
  have hleft : fkRectConfigurationGraphEquiv R ⁻¹'
        (fkRectGraphForceOpen R J ⁻¹' B) =
      fkRectForceEdgesOpen R I ⁻¹' A := by
    ext omega
    simp only [Set.mem_preimage]
    rw [← fkRectConfigurationGraphEquiv_forceEdgesOpen R I omega]
    simp [B]
  rwa [hleft, hright] at hpush

theorem fkRectForceEdgesClosed_torusCut
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectForceEdgesClosed R (fkRectTorusCutEdges R) omega =
      fkRectForceCutClosed R omega := by
  rfl


theorem fkRectCritical_cutPushforward_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) *
        fkRectCriticalEventMass R q
          (fkRectForceCutClosed R ⁻¹' A) ≤
      fkRectCriticalEventMass R q A := by
  have hbase :=
    fkRectCritical_cFE_pow_mul_forceEdgesClosed_preimage_le_event
      R hq (fkRectTorusCutEdges R) A
  rw [show fkRectForceEdgesClosed R (fkRectTorusCutEdges R) =
      fkRectForceCutClosed R by
    funext omega
    exact fkRectForceEdgesClosed_torusCut R omega] at hbase
  have hpow : FK.cFE (fkRectCriticalP q) q ^
        (2 * R.width + R.height) ≤
      FK.cFE (fkRectCriticalP q) q ^
        (fkRectTorusCutEdges R).card :=
    pow_le_pow_of_le_one (fkRectCritical_cFE_nonneg hq)
      (fkRectCritical_cFE_le_one hq)
      (fkRectTorusCutEdges_card_le R)
  exact (mul_le_mul_of_nonneg_right hpow
    (fkRectCriticalEventMass_nonneg R
      (lt_of_lt_of_le zero_lt_one hq) _)).trans hbase

theorem fkRectCriticalZeroTurnAboveMass_eq_eventMass
    (R : FKRectTorus) (q : Real) (L : Nat) :
    fkRectCriticalZeroTurnAboveMass R q L =
      fkRectCriticalEventMass R q
        {omega | L < fkRectZeroTurnLoopCount R omega} := by
  unfold fkRectCriticalZeroTurnAboveMass fkRectCriticalEventMass
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases habove : L < fkRectZeroTurnLoopCount R omega <;>
    simp [Set.indicator, habove]


theorem fkRectCritical_zeroTurnAbove_cut_transfer
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (K : R.Configuration → Nat)
    (htop : ∀ omega : R.Configuration,
      fkRectZeroTurnLoopCount R omega ≤
        2 * R.width + K (fkRectForceCutClosed R omega))
    (n : Nat) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) *
        fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) ≤
      fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧ n < K eta} := by
  let Bad : Set R.Configuration :=
    {omega | 2 * R.width + n < fkRectZeroTurnLoopCount R omega}
  let Crossing : Set R.Configuration :=
    {eta | FKRectCutClosedConfiguration R eta ∧ n < K eta}
  have hsubset : Bad ⊆ fkRectForceCutClosed R ⁻¹' Crossing := by
    intro omega homega
    change FKRectCutClosedConfiguration R
        (fkRectForceCutClosed R omega) ∧
      n < K (fkRectForceCutClosed R omega)
    refine ⟨fkRectCutClosedConfiguration_forceCutClosed R omega, ?_⟩
    have hbound := htop omega
    change 2 * R.width + n < fkRectZeroTurnLoopCount R omega at homega
    omega
  rw [fkRectCriticalZeroTurnAboveMass_eq_eventMass]
  change FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) *
      fkRectCriticalEventMass R q Bad ≤
    fkRectCriticalEventMass R q Crossing
  calc
    _ ≤ FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) *
          fkRectCriticalEventMass R q
            (fkRectForceCutClosed R ⁻¹' Crossing) :=
      mul_le_mul_of_nonneg_left
        (fkRectCriticalEventMass_mono R
          (lt_of_lt_of_le zero_lt_one hq) hsubset)
        (pow_nonneg (fkRectCritical_cFE_nonneg hq) _)
    _ ≤ fkRectCriticalEventMass R q Crossing :=
      fkRectCritical_cutPushforward_event R hq Crossing

end
end StatMech.FrontierD
