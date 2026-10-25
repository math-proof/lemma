/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part11


namespace StatMech

namespace Exact3D

theorem freeSelectedPositiveSubcriticalCorrelationLength_spec
    (h : FreePositiveSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    0 < freeSelectedPositiveSubcriticalCorrelationLength h β ∧
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
        (freeSelectedPositiveSubcriticalCorrelationLength h β) := by
  unfold freeSelectedPositiveSubcriticalCorrelationLength
  rw [dif_pos hβpos, dif_pos hβc]
  exact Classical.choose_spec (h β hβpos hβc)


theorem freeSelectedPositiveSubcriticalCorrelationLength_pos
    (h : FreePositiveSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    0 < freeSelectedPositiveSubcriticalCorrelationLength h β :=
  (freeSelectedPositiveSubcriticalCorrelationLength_spec h hβpos hβc).1


theorem freeSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength
    (h : FreePositiveSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
      (freeSelectedPositiveSubcriticalCorrelationLength h β) :=
  (freeSelectedPositiveSubcriticalCorrelationLength_spec h hβpos hβc).2


theorem plusSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength
    (h : PlusPositiveSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    plusSelectedPositiveSubcriticalCorrelationLength h β =
      liminfCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay :=
  (plusSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength
    h hβpos hβc).liminfCorrelationLength_eq.symm


theorem freeSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength
    (h : FreePositiveSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    freeSelectedPositiveSubcriticalCorrelationLength h β =
      liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay :=
  (freeSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength
    h hβpos hβc).liminfCorrelationLength_eq.symm


theorem eventually_mem_positiveSubcriticalWindow {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) := by
  filter_upwards
    [Ioo_mem_nhdsLT (show Ising.betaC 3 - δ < Ising.betaC 3 by
      linarith)] with β hβ
  exact hβ


theorem beta_pos_of_mem_positiveSubcriticalWindow
    {δ β : ℝ} (hδle : δ ≤ Ising.betaC 3)
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
    0 < β := by
  have hnonneg : 0 ≤ Ising.betaC 3 - δ := sub_nonneg.mpr hδle
  linarith [hβ.1, hnonneg]


theorem
    eventually_plusSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
    (h : PlusPositiveSubcriticalMassBridge) {δ : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      plusSelectedPositiveSubcriticalCorrelationLengthFromMass h β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay := by
  filter_upwards [eventually_mem_positiveSubcriticalWindow hδ] with β hβ
  exact
    plusSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
      h (beta_pos_of_mem_positiveSubcriticalWindow hδle hβ) hβ.2


theorem
    eventually_freeSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
    (h : FreePositiveSubcriticalMassBridge) {δ : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      freeSelectedPositiveSubcriticalCorrelationLengthFromMass h β =
        liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
          ising3DXAxisRay := by
  filter_upwards [eventually_mem_positiveSubcriticalWindow hδ] with β hβ
  exact
    freeSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
      h (beta_pos_of_mem_positiveSubcriticalWindow hδle hβ) hβ.2


theorem
    eventually_plusSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength
    (h : PlusPositiveSubcriticalCorrelationLengthBridge) {δ : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      plusSelectedPositiveSubcriticalCorrelationLength h β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay := by
  filter_upwards [eventually_mem_positiveSubcriticalWindow hδ] with β hβ
  exact
    plusSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength
      h (beta_pos_of_mem_positiveSubcriticalWindow hδle hβ) hβ.2


theorem
    eventually_freeSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength
    (h : FreePositiveSubcriticalCorrelationLengthBridge) {δ : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      freeSelectedPositiveSubcriticalCorrelationLength h β =
        liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
          ising3DXAxisRay := by
  filter_upwards [eventually_mem_positiveSubcriticalWindow hδ] with β hβ
  exact
    freeSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength
      h (beta_pos_of_mem_positiveSubcriticalWindow hδle hβ) hβ.2


theorem
    plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminf
    (h : PlusPositiveSubcriticalMassBridge) {δ ν : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    HasCriticalNu Ising3DModel
        (plusSelectedPositiveSubcriticalCorrelationLengthFromMass h) ν ↔
      HasCriticalNu Ising3DModel
        (fun β =>
          liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay) ν := by
  refine HasCriticalNu.congr_eventually_iff ?_
  exact
    (eventually_plusSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
      h hδ hδle).mono fun _ hβ => hβ.symm


theorem
    freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminf
    (h : FreePositiveSubcriticalMassBridge) {δ ν : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    HasCriticalNu Ising3DFreeModel
        (freeSelectedPositiveSubcriticalCorrelationLengthFromMass h) ν ↔
      HasCriticalNu Ising3DFreeModel
        (fun β =>
          liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
            ising3DXAxisRay) ν := by
  refine HasCriticalNu.congr_eventually_iff ?_
  exact
    (eventually_freeSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
      h hδ hδle).mono fun _ hβ => hβ.symm


theorem
    plusSelectedPositiveSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength
    (h : PlusPositiveSubcriticalCorrelationLengthBridge) {δ ν : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    HasCriticalNu Ising3DModel
        (plusSelectedPositiveSubcriticalCorrelationLength h) ν ↔
      HasCriticalNu Ising3DModel
        (fun β =>
          liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay) ν := by
  refine HasCriticalNu.congr_eventually_iff ?_
  exact
    (eventually_plusSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength
      h hδ hδle).mono fun _ hβ => hβ.symm


theorem
    freeSelectedPositiveSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength
    (h : FreePositiveSubcriticalCorrelationLengthBridge) {δ ν : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    HasCriticalNu Ising3DFreeModel
        (freeSelectedPositiveSubcriticalCorrelationLength h) ν ↔
      HasCriticalNu Ising3DFreeModel
        (fun β =>
          liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
            ising3DXAxisRay) ν := by
  refine HasCriticalNu.congr_eventually_iff ?_
  exact
    (eventually_freeSelectedPositiveSubcriticalCorrelationLength_eq_liminfCorrelationLength
      h hδ hδle).mono fun _ hβ => hβ.symm


end Exact3D
end StatMech
