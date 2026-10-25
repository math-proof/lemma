/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17


namespace StatMech

namespace Exact3D

theorem freeSelectedSubcriticalCorrelationLength_spec
    (h : FreeSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβ : β < Ising.betaC 3) :
    0 < freeSelectedSubcriticalCorrelationLength h β ∧
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
        (freeSelectedSubcriticalCorrelationLength h β) := by
  unfold freeSelectedSubcriticalCorrelationLength
  rw [dif_pos hβ]
  exact Classical.choose_spec (h β hβ)


theorem freeSelectedSubcriticalCorrelationLength_pos
    (h : FreeSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβ : β < Ising.betaC 3) :
    0 < freeSelectedSubcriticalCorrelationLength h β :=
  (freeSelectedSubcriticalCorrelationLength_spec h hβ).1


theorem freeSelectedSubcriticalCorrelationLength_hasCorrelationLength
    (h : FreeSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβ : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
      (freeSelectedSubcriticalCorrelationLength h β) :=
  (freeSelectedSubcriticalCorrelationLength_spec h hβ).2


theorem plusSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength
    (h : PlusSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβ : β < Ising.betaC 3) :
    plusSelectedSubcriticalCorrelationLength h β =
      liminfCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay :=
  (plusSelectedSubcriticalCorrelationLength_hasCorrelationLength
    h hβ).liminfCorrelationLength_eq.symm


theorem freeSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength
    (h : FreeSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβ : β < Ising.betaC 3) :
    freeSelectedSubcriticalCorrelationLength h β =
      liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay :=
  (freeSelectedSubcriticalCorrelationLength_hasCorrelationLength
    h hβ).liminfCorrelationLength_eq.symm


theorem eventually_plusSelectedSubcriticalMass_pos
    (h : PlusSubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < plusSelectedSubcriticalMass h β := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact plusSelectedSubcriticalMass_pos h hβ


theorem eventually_plusSelectedSubcriticalMass_hasInverseCorrelationLength
    (h : PlusSubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (plusSelectedSubcriticalMass h β) := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact plusSelectedSubcriticalMass_hasInverseCorrelationLength h hβ


theorem eventually_plusSelectedSubcriticalCorrelationLengthFromMass_pos
    (h : PlusSubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < plusSelectedSubcriticalCorrelationLengthFromMass h β := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact plusSelectedSubcriticalCorrelationLengthFromMass_pos h hβ


theorem eventually_plusSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength
    (h : PlusSubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (plusSelectedSubcriticalCorrelationLengthFromMass h β) := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact
    plusSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength h hβ


theorem eventually_plusSelectedSubcriticalCorrelationLength_pos
    (h : PlusSubcriticalCorrelationLengthBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < plusSelectedSubcriticalCorrelationLength h β := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact plusSelectedSubcriticalCorrelationLength_pos h hβ


theorem eventually_plusSelectedSubcriticalCorrelationLength_hasCorrelationLength
    (h : PlusSubcriticalCorrelationLengthBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (plusSelectedSubcriticalCorrelationLength h β) := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact plusSelectedSubcriticalCorrelationLength_hasCorrelationLength h hβ


theorem eventually_freeSelectedSubcriticalMass_pos
    (h : FreeSubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < freeSelectedSubcriticalMass h β := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact freeSelectedSubcriticalMass_pos h hβ


theorem eventually_freeSelectedSubcriticalMass_hasInverseCorrelationLength
    (h : FreeSubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay (freeSelectedSubcriticalMass h β) := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact freeSelectedSubcriticalMass_hasInverseCorrelationLength h hβ


theorem eventually_freeSelectedSubcriticalCorrelationLengthFromMass_pos
    (h : FreeSubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < freeSelectedSubcriticalCorrelationLengthFromMass h β := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact freeSelectedSubcriticalCorrelationLengthFromMass_pos h hβ


theorem eventually_freeSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength
    (h : FreeSubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
        (freeSelectedSubcriticalCorrelationLengthFromMass h β) := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact
    freeSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength h hβ


theorem eventually_freeSelectedSubcriticalCorrelationLength_pos
    (h : FreeSubcriticalCorrelationLengthBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < freeSelectedSubcriticalCorrelationLength h β := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact freeSelectedSubcriticalCorrelationLength_pos h hβ


theorem eventually_freeSelectedSubcriticalCorrelationLength_hasCorrelationLength
    (h : FreeSubcriticalCorrelationLengthBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
        (freeSelectedSubcriticalCorrelationLength h β) := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact freeSelectedSubcriticalCorrelationLength_hasCorrelationLength h hβ


theorem
    eventually_plusSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
    (h : PlusSubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      plusSelectedSubcriticalCorrelationLengthFromMass h β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact
    plusSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
      h hβ


theorem
    eventually_freeSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
    (h : FreeSubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      freeSelectedSubcriticalCorrelationLengthFromMass h β =
        liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
          ising3DXAxisRay := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact
    freeSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
      h hβ


theorem eventually_plusSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength
    (h : PlusSubcriticalCorrelationLengthBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      plusSelectedSubcriticalCorrelationLength h β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact plusSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength h hβ


theorem eventually_freeSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength
    (h : FreeSubcriticalCorrelationLengthBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      freeSelectedSubcriticalCorrelationLength h β =
        liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
          ising3DXAxisRay := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact freeSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength h hβ


theorem
    plusSelectedSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminfCorrelationLength
    (h : PlusSubcriticalMassBridge) {ν : ℝ} :
    HasCriticalNu Ising3DModel
        (plusSelectedSubcriticalCorrelationLengthFromMass h) ν ↔
      HasCriticalNu Ising3DModel
        (fun β =>
          liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay) ν := by
  refine HasCriticalNu.congr_eventually_iff ?_
  exact
    (eventually_plusSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
      h).mono fun _ hβ => hβ.symm


theorem
    freeSelectedSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminfCorrelationLength
    (h : FreeSubcriticalMassBridge) {ν : ℝ} :
    HasCriticalNu Ising3DFreeModel
        (freeSelectedSubcriticalCorrelationLengthFromMass h) ν ↔
      HasCriticalNu Ising3DFreeModel
        (fun β =>
          liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
            ising3DXAxisRay) ν := by
  refine HasCriticalNu.congr_eventually_iff ?_
  exact
    (eventually_freeSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
      h).mono fun _ hβ => hβ.symm


theorem
    plusSelectedSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength
    (h : PlusSubcriticalCorrelationLengthBridge) {ν : ℝ} :
    HasCriticalNu Ising3DModel
        (plusSelectedSubcriticalCorrelationLength h) ν ↔
      HasCriticalNu Ising3DModel
        (fun β =>
          liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay) ν := by
  refine HasCriticalNu.congr_eventually_iff ?_
  exact
    (eventually_plusSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength
      h).mono fun _ hβ => hβ.symm


theorem
    freeSelectedSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength
    (h : FreeSubcriticalCorrelationLengthBridge) {ν : ℝ} :
    HasCriticalNu Ising3DFreeModel
        (freeSelectedSubcriticalCorrelationLength h) ν ↔
      HasCriticalNu Ising3DFreeModel
        (fun β =>
          liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
            ising3DXAxisRay) ν := by
  refine HasCriticalNu.congr_eventually_iff ?_
  exact
    (eventually_freeSelectedSubcriticalCorrelationLength_eq_liminfCorrelationLength
      h).mono fun _ hβ => hβ.symm


theorem Ising3DFreeModel_twoPoint_eq (β : ℝ) (x y : Ising3DSite) :
    TwoPointFunction Ising3DFreeModel β x y = ising3DFreeTwoPoint β x y :=
  rfl


theorem Ising3DFreeModel_betaC_eq :
    Ising3DFreeModel.betaC = Ising.betaC 3 :=
  rfl


theorem Ising3DFreeModel_inverseDecayRate_xAxis_eq (β : ℝ) (n : ℕ) :
    inverseDecayRate Ising3DFreeModel β ising3DOrigin ising3DXAxisRay n =
      freeInverseDecayRateOnXAxis β n := by
  rfl


theorem Ising3DFreeModel_lowerInverseCorrelationLength_xAxis_eq (β : ℝ) :
    lowerInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay =
      freeLowerInverseCorrelationLengthOnXAxis β := by
  rfl


theorem Ising3DFreeModel_upperInverseCorrelationLength_xAxis_eq (β : ℝ) :
    upperInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay =
      freeUpperInverseCorrelationLengthOnXAxis β := by
  rfl


theorem Ising3DFreeModel_liminfCorrelationLength_xAxis_eq (β : ℝ) :
    liminfCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay =
      freeLiminfCorrelationLengthOnXAxis β := by
  rfl


theorem plus_hasInverseCorrelationLength_xAxis_of_exactExponential
    {β A m : ℝ} (hA : 0 < A)
    (hG : PlusXAxisExactExponentialDecay β A m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m := by
  refine hasInverseCorrelationLength_of_eventually_abs_eq_exp
    Ising3DModel β ising3DOrigin ising3DXAxisRay hA ?_
  filter_upwards [hG] with n hn
  simpa [PlusXAxisExactExponentialDecay, TwoPointAlongRay, twoPointOnXAxis,
    twoPointAtDisplacement, Ising3DModel] using hn


theorem free_hasInverseCorrelationLength_xAxis_of_exactExponential
    {β A m : ℝ} (hA : 0 < A)
    (hG : FreeXAxisExactExponentialDecay β A m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m := by
  refine hasInverseCorrelationLength_of_eventually_abs_eq_exp
    Ising3DFreeModel β ising3DOrigin ising3DXAxisRay hA ?_
  filter_upwards [hG] with n hn
  simpa [FreeXAxisExactExponentialDecay, TwoPointAlongRay, freeTwoPointOnXAxis,
    freeTwoPointAtDisplacement, Ising3DFreeModel] using hn


theorem plus_hasCorrelationLength_xAxis_of_exactExponential
    {β A m : ℝ} (hA : 0 < A) (hm : 0 < m)
    (hG : PlusXAxisExactExponentialDecay β A m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
  refine hasCorrelationLength_of_eventually_abs_eq_exp
    Ising3DModel β ising3DOrigin ising3DXAxisRay hA hm ?_
  filter_upwards [hG] with n hn
  simpa [PlusXAxisExactExponentialDecay, TwoPointAlongRay, twoPointOnXAxis,
    twoPointAtDisplacement, Ising3DModel] using hn


theorem free_hasCorrelationLength_xAxis_of_exactExponential
    {β A m : ℝ} (hA : 0 < A) (hm : 0 < m)
    (hG : FreeXAxisExactExponentialDecay β A m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
  refine hasCorrelationLength_of_eventually_abs_eq_exp
    Ising3DFreeModel β ising3DOrigin ising3DXAxisRay hA hm ?_
  filter_upwards [hG] with n hn
  simpa [FreeXAxisExactExponentialDecay, TwoPointAlongRay, freeTwoPointOnXAxis,
    freeTwoPointAtDisplacement, Ising3DFreeModel] using hn


theorem plus_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ}
    (hG : PlusXAxisSubexponentialPrefactorDecay β A m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m := by
  refine hasInverseCorrelationLength_of_eventually_abs_eq_prefactor_exp
    Ising3DModel β ising3DOrigin ising3DXAxisRay hG.1 hG.2.1 ?_
  filter_upwards [hG.2.2] with n hn
  simpa [PlusXAxisSubexponentialPrefactorDecay, TwoPointAlongRay, twoPointOnXAxis,
    twoPointAtDisplacement, Ising3DModel] using hn


theorem free_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ}
    (hG : FreeXAxisSubexponentialPrefactorDecay β A m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m := by
  refine hasInverseCorrelationLength_of_eventually_abs_eq_prefactor_exp
    Ising3DFreeModel β ising3DOrigin ising3DXAxisRay hG.1 hG.2.1 ?_
  filter_upwards [hG.2.2] with n hn
  simpa [FreeXAxisSubexponentialPrefactorDecay, TwoPointAlongRay, freeTwoPointOnXAxis,
    freeTwoPointAtDisplacement, Ising3DFreeModel] using hn


theorem plus_hasCorrelationLength_xAxis_of_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hm : 0 < m)
    (hG : PlusXAxisSubexponentialPrefactorDecay β A m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
  refine hasCorrelationLength_of_eventually_abs_eq_prefactor_exp
    Ising3DModel β ising3DOrigin ising3DXAxisRay hG.1 hG.2.1 hm ?_
  filter_upwards [hG.2.2] with n hn
  simpa [PlusXAxisSubexponentialPrefactorDecay, TwoPointAlongRay, twoPointOnXAxis,
    twoPointAtDisplacement, Ising3DModel] using hn


theorem free_hasCorrelationLength_xAxis_of_subexponentialPrefactor
    {β m : ℝ} {A : ℕ → ℝ} (hm : 0 < m)
    (hG : FreeXAxisSubexponentialPrefactorDecay β A m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
  refine hasCorrelationLength_of_eventually_abs_eq_prefactor_exp
    Ising3DFreeModel β ising3DOrigin ising3DXAxisRay hG.1 hG.2.1 hm ?_
  filter_upwards [hG.2.2] with n hn
  simpa [FreeXAxisSubexponentialPrefactorDecay, TwoPointAlongRay, freeTwoPointOnXAxis,
    freeTwoPointAtDisplacement, Ising3DFreeModel] using hn


theorem plus_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds
    {β m : ℝ} {Alo Ahi : ℕ → ℝ}
    (hG : PlusXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m := by
  refine hasInverseCorrelationLength_of_eventually_abs_between_prefactor_exp
    Ising3DModel β ising3DOrigin ising3DXAxisRay
    hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 ?_ ?_
  · filter_upwards [hG.2.2.2.2.1] with n hn
    simpa [PlusXAxisTwoSidedSubexponentialBounds, TwoPointAlongRay, twoPointOnXAxis,
      twoPointAtDisplacement, Ising3DModel] using hn
  · filter_upwards [hG.2.2.2.2.2] with n hn
    simpa [PlusXAxisTwoSidedSubexponentialBounds, TwoPointAlongRay, twoPointOnXAxis,
      twoPointAtDisplacement, Ising3DModel] using hn


theorem free_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds
    {β m : ℝ} {Alo Ahi : ℕ → ℝ}
    (hG : FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m := by
  refine hasInverseCorrelationLength_of_eventually_abs_between_prefactor_exp
    Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
    hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 ?_ ?_
  · filter_upwards [hG.2.2.2.2.1] with n hn
    simpa [FreeXAxisTwoSidedSubexponentialBounds, TwoPointAlongRay,
      freeTwoPointOnXAxis, freeTwoPointAtDisplacement, Ising3DFreeModel] using hn
  · filter_upwards [hG.2.2.2.2.2] with n hn
    simpa [FreeXAxisTwoSidedSubexponentialBounds, TwoPointAlongRay,
      freeTwoPointOnXAxis, freeTwoPointAtDisplacement, Ising3DFreeModel] using hn


theorem plus_hasCorrelationLength_xAxis_of_twoSidedSubexponentialBounds
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hm : 0 < m)
    (hG : PlusXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
  refine hasCorrelationLength_of_eventually_abs_between_prefactor_exp
    Ising3DModel β ising3DOrigin ising3DXAxisRay
    hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 hm ?_ ?_
  · filter_upwards [hG.2.2.2.2.1] with n hn
    simpa [PlusXAxisTwoSidedSubexponentialBounds, TwoPointAlongRay, twoPointOnXAxis,
      twoPointAtDisplacement, Ising3DModel] using hn
  · filter_upwards [hG.2.2.2.2.2] with n hn
    simpa [PlusXAxisTwoSidedSubexponentialBounds, TwoPointAlongRay, twoPointOnXAxis,
      twoPointAtDisplacement, Ising3DModel] using hn


theorem free_hasCorrelationLength_xAxis_of_twoSidedSubexponentialBounds
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hm : 0 < m)
    (hG : FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m⁻¹ := by
  refine hasCorrelationLength_of_eventually_abs_between_prefactor_exp
    Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
    hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 hm ?_ ?_
  · filter_upwards [hG.2.2.2.2.1] with n hn
    simpa [FreeXAxisTwoSidedSubexponentialBounds, TwoPointAlongRay,
      freeTwoPointOnXAxis, freeTwoPointAtDisplacement, Ising3DFreeModel] using hn
  · filter_upwards [hG.2.2.2.2.2] with n hn
    simpa [FreeXAxisTwoSidedSubexponentialBounds, TwoPointAlongRay,
      freeTwoPointOnXAxis, freeTwoPointAtDisplacement, Ising3DFreeModel] using hn


theorem plusXAxisExactExponentialDecay_of_fkConnectionComparison
    {β A m : ℝ} {conn : ℕ → ℝ}
    (hcmp : PlusXAxisFKConnectionAgrees β conn)
    (hconn : FKXAxisConnectionExactExponentialDecay conn A m) :
    PlusXAxisExactExponentialDecay β A m := by
  filter_upwards [hcmp, hconn] with n hcmpn hconnn
  exact hcmpn.trans hconnn


theorem freeXAxisExactExponentialDecay_of_fkConnectionComparison
    {β A m : ℝ} {conn : ℕ → ℝ}
    (hcmp : FreeXAxisFKConnectionAgrees β conn)
    (hconn : FKXAxisConnectionExactExponentialDecay conn A m) :
    FreeXAxisExactExponentialDecay β A m := by
  filter_upwards [hcmp, hconn] with n hcmpn hconnn
  exact hcmpn.trans hconnn


theorem plusXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison
    {β m : ℝ} {conn A : ℕ → ℝ}
    (hcmp : PlusXAxisFKConnectionAgrees β conn)
    (hconn : FKXAxisConnectionSubexponentialPrefactorDecay conn A m) :
    PlusXAxisSubexponentialPrefactorDecay β A m := by
  refine ⟨hconn.1, hconn.2.1, ?_⟩
  filter_upwards [hcmp, hconn.2.2] with n hcmpn hconnn
  exact hcmpn.trans hconnn


theorem freeXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison
    {β m : ℝ} {conn A : ℕ → ℝ}
    (hcmp : FreeXAxisFKConnectionAgrees β conn)
    (hconn : FKXAxisConnectionSubexponentialPrefactorDecay conn A m) :
    FreeXAxisSubexponentialPrefactorDecay β A m := by
  refine ⟨hconn.1, hconn.2.1, ?_⟩
  filter_upwards [hcmp, hconn.2.2] with n hcmpn hconnn
  exact hcmpn.trans hconnn


theorem plusXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison
    {β m : ℝ} {conn Alo Ahi : ℕ → ℝ}
    (hcmp : PlusXAxisFKConnectionAgrees β conn)
    (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m) :
    PlusXAxisTwoSidedSubexponentialBounds β Alo Ahi m := by
  refine
    ⟨hconn.1, hconn.2.1, hconn.2.2.1, hconn.2.2.2.1, ?_, ?_⟩
  · filter_upwards [hcmp, hconn.2.2.2.2.1] with n hcmpn hconnn
    calc
      Alo n * Real.exp (-(m * (n : ℝ))) ≤ conn n := hconnn
      _ = |twoPointOnXAxis β n| := hcmpn.symm
  · filter_upwards [hcmp, hconn.2.2.2.2.2] with n hcmpn hconnn
    calc
      |twoPointOnXAxis β n| = conn n := hcmpn
      _ ≤ Ahi n * Real.exp (-(m * (n : ℝ))) := hconnn


theorem freeXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison
    {β m : ℝ} {conn Alo Ahi : ℕ → ℝ}
    (hcmp : FreeXAxisFKConnectionAgrees β conn)
    (hconn : FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m) :
    FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi m := by
  refine
    ⟨hconn.1, hconn.2.1, hconn.2.2.1, hconn.2.2.2.1, ?_, ?_⟩
  · filter_upwards [hcmp, hconn.2.2.2.2.1] with n hcmpn hconnn
    calc
      Alo n * Real.exp (-(m * (n : ℝ))) ≤ conn n := hconnn
      _ = |freeTwoPointOnXAxis β n| := hcmpn.symm
  · filter_upwards [hcmp, hconn.2.2.2.2.2] with n hcmpn hconnn
    calc
      |freeTwoPointOnXAxis β n| = conn n := hcmpn
      _ ≤ Ahi n * Real.exp (-(m * (n : ℝ))) := hconnn


theorem plus_hasInverseCorrelationLength_of_free_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) {β m : ℝ}
    (hβ : β < Ising.betaC 3)
    {origin : Ising3DSite} {ray : ℕ → Ising3DSite}
    (hfree :
      HasInverseCorrelationLength Ising3DFreeModel β origin ray m) :
    HasInverseCorrelationLength Ising3DModel β origin ray m := by
  refine hfree.congr_eventually ?_
  filter_upwards with n
  simpa [TwoPointAlongRay, Ising3DFreeModel, Ising3DModel] using
    (hagree β hβ origin (ray n)).symm


theorem plus_hasCorrelationLength_of_free_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) {β ξ : ℝ}
    (hβ : β < Ising.betaC 3)
    {origin : Ising3DSite} {ray : ℕ → Ising3DSite}
    (hfree :
      HasCorrelationLength Ising3DFreeModel β origin ray ξ) :
    HasCorrelationLength Ising3DModel β origin ray ξ := by
  refine hfree.congr_eventually ?_
  filter_upwards with n
  simpa [TwoPointAlongRay, Ising3DFreeModel, Ising3DModel] using
    (hagree β hβ origin (ray n)).symm


theorem free_hasInverseCorrelationLength_of_plus_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) {β m : ℝ}
    (hβ : β < Ising.betaC 3)
    {origin : Ising3DSite} {ray : ℕ → Ising3DSite}
    (hplus :
      HasInverseCorrelationLength Ising3DModel β origin ray m) :
    HasInverseCorrelationLength Ising3DFreeModel β origin ray m := by
  refine hplus.congr_eventually ?_
  filter_upwards with n
  simpa [TwoPointAlongRay, Ising3DFreeModel, Ising3DModel] using
    hagree β hβ origin (ray n)


theorem free_hasCorrelationLength_of_plus_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) {β ξ : ℝ}
    (hβ : β < Ising.betaC 3)
    {origin : Ising3DSite} {ray : ℕ → Ising3DSite}
    (hplus :
      HasCorrelationLength Ising3DModel β origin ray ξ) :
    HasCorrelationLength Ising3DFreeModel β origin ray ξ := by
  refine hplus.congr_eventually ?_
  filter_upwards with n
  simpa [TwoPointAlongRay, Ising3DFreeModel, Ising3DModel] using
    hagree β hβ origin (ray n)


theorem hasInverseCorrelationLength_plus_free_agree_iff
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) {β m : ℝ}
    (hβ : β < Ising.betaC 3)
    {origin : Ising3DSite} {ray : ℕ → Ising3DSite} :
    HasInverseCorrelationLength Ising3DModel β origin ray m ↔
      HasInverseCorrelationLength Ising3DFreeModel β origin ray m :=
  ⟨free_hasInverseCorrelationLength_of_plus_agree hagree hβ,
    plus_hasInverseCorrelationLength_of_free_agree hagree hβ⟩


theorem hasCorrelationLength_plus_free_agree_iff
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) {β ξ : ℝ}
    (hβ : β < Ising.betaC 3)
    {origin : Ising3DSite} {ray : ℕ → Ising3DSite} :
    HasCorrelationLength Ising3DModel β origin ray ξ ↔
      HasCorrelationLength Ising3DFreeModel β origin ray ξ :=
  ⟨free_hasCorrelationLength_of_plus_agree hagree hβ,
    plus_hasCorrelationLength_of_free_agree hagree hβ⟩


theorem plus_hasInverseCorrelationLength_xAxis_of_free_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) {β m : ℝ}
    (hβ : β < Ising.betaC 3)
    (hfree :
      HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay m) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay m :=
  plus_hasInverseCorrelationLength_of_free_agree hagree hβ hfree


theorem plus_hasCorrelationLength_xAxis_of_free_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) {β ξ : ℝ}
    (hβ : β < Ising.betaC 3)
    (hfree :
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay ξ) :
    HasCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay ξ :=
  plus_hasCorrelationLength_of_free_agree hagree hβ hfree


theorem free_hasInverseCorrelationLength_xAxis_of_plus_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) {β m : ℝ}
    (hβ : β < Ising.betaC 3)
    (hplus :
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay m) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay m :=
  free_hasInverseCorrelationLength_of_plus_agree hagree hβ hplus


theorem free_hasCorrelationLength_xAxis_of_plus_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) {β ξ : ℝ}
    (hβ : β < Ising.betaC 3)
    (hplus :
      HasCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay ξ) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay ξ :=
  free_hasCorrelationLength_of_plus_agree hagree hβ hplus


theorem hasInverseCorrelationLength_xAxis_plus_free_agree_iff
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) {β m : ℝ}
    (hβ : β < Ising.betaC 3) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay m ↔
      HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay m :=
  hasInverseCorrelationLength_plus_free_agree_iff hagree hβ


theorem hasCorrelationLength_xAxis_plus_free_agree_iff
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) {β ξ : ℝ}
    (hβ : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay ξ ↔
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay ξ :=
  hasCorrelationLength_plus_free_agree_iff hagree hβ


theorem liminfCorrelationLength_plus_eq_free_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) {β : ℝ}
    (hβ : β < Ising.betaC 3)
    {origin : Ising3DSite} {ray : ℕ → Ising3DSite} :
    liminfCorrelationLength Ising3DModel β origin ray =
      liminfCorrelationLength Ising3DFreeModel β origin ray := by
  refine liminfCorrelationLength_congr_eventually ?_
  filter_upwards with n
  simpa [TwoPointAlongRay, Ising3DModel, Ising3DFreeModel] using
    hagree β hβ origin (ray n)


theorem eventually_liminfCorrelationLength_xAxis_plus_eq_free_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay =
        liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
          ising3DXAxisRay := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact liminfCorrelationLength_plus_eq_free_of_agree hagree hβ


theorem liminfCorrelationLength_xAxis_hasCriticalNu_plus_free_agree_iff
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) {ν : ℝ} :
    HasCriticalNu Ising3DModel
        (fun β =>
          liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay) ν ↔
      HasCriticalNu Ising3DFreeModel
        (fun β =>
          liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
            ising3DXAxisRay) ν := by
  refine
    HasCriticalNu.liminfCorrelationLength_congr_eventually_iff
      (M := Ising3DModel) (N := Ising3DFreeModel)
      (origin := ising3DOrigin) (ray := ising3DXAxisRay) (ν := ν)
      rfl ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  filter_upwards with n
  simpa [TwoPointAlongRay, Ising3DModel, Ising3DFreeModel] using
    hagree β hβ ising3DOrigin (ising3DXAxisRay n)


theorem freePosSubcriticalLengthFromMass_hasCriticalNu_iff_plus_liminf_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreePositiveSubcriticalMassBridge) {δ ν : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    HasCriticalNu Ising3DFreeModel
        (freeSelectedPositiveSubcriticalCorrelationLengthFromMass h) ν ↔
      HasCriticalNu Ising3DModel
        (fun β =>
          liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay) ν :=
  (freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminf
    h hδ hδle).trans
    (liminfCorrelationLength_xAxis_hasCriticalNu_plus_free_agree_iff
      hagree).symm


theorem freePosSubcriticalLength_hasCriticalNu_iff_plus_liminf_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreePositiveSubcriticalCorrelationLengthBridge) {δ ν : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    HasCriticalNu Ising3DFreeModel
        (freeSelectedPositiveSubcriticalCorrelationLength h) ν ↔
      HasCriticalNu Ising3DModel
        (fun β =>
          liminfCorrelationLength Ising3DModel β ising3DOrigin
            ising3DXAxisRay) ν :=
  (freeSelectedPositiveSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength
    h hδ hδle).trans
    (liminfCorrelationLength_xAxis_hasCriticalNu_plus_free_agree_iff
      hagree).symm


theorem plusPosSubcriticalLengthFromMass_hasCriticalNu_iff_free_liminf_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : PlusPositiveSubcriticalMassBridge) {δ ν : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    HasCriticalNu Ising3DModel
        (plusSelectedPositiveSubcriticalCorrelationLengthFromMass h) ν ↔
      HasCriticalNu Ising3DFreeModel
        (fun β =>
          liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
            ising3DXAxisRay) ν :=
  (plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCriticalNu_iff_liminf
    h hδ hδle).trans
    (liminfCorrelationLength_xAxis_hasCriticalNu_plus_free_agree_iff
      hagree)


theorem plusPosSubcriticalLength_hasCriticalNu_iff_free_liminf_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : PlusPositiveSubcriticalCorrelationLengthBridge) {δ ν : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    HasCriticalNu Ising3DModel
        (plusSelectedPositiveSubcriticalCorrelationLength h) ν ↔
      HasCriticalNu Ising3DFreeModel
        (fun β =>
          liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
            ising3DXAxisRay) ν :=
  (plusSelectedPositiveSubcriticalCorrelationLength_hasCriticalNu_iff_liminfCorrelationLength
    h hδ hδle).trans
    (liminfCorrelationLength_xAxis_hasCriticalNu_plus_free_agree_iff
      hagree)


theorem freeSelectedSubcriticalMass_hasPlusInverseCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreeSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay (freeSelectedSubcriticalMass h β) :=
  plus_hasInverseCorrelationLength_xAxis_of_free_agree hagree hβ
    (freeSelectedSubcriticalMass_hasInverseCorrelationLength h hβ)


theorem
    freeSelectedSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreeSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (freeSelectedSubcriticalCorrelationLengthFromMass h β) :=
  plus_hasCorrelationLength_xAxis_of_free_agree hagree hβ
    (freeSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength h hβ)


theorem freeSelectedSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreeSubcriticalCorrelationLengthBridge)
    {β : ℝ} (hβ : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (freeSelectedSubcriticalCorrelationLength h β) :=
  plus_hasCorrelationLength_xAxis_of_free_agree hagree hβ
    (freeSelectedSubcriticalCorrelationLength_hasCorrelationLength h hβ)


theorem
    eventually_freeSelectedSubcriticalMass_hasPlusInverseCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreeSubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (freeSelectedSubcriticalMass h β) := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact
    freeSelectedSubcriticalMass_hasPlusInverseCorrelationLength_of_agree
      hagree h hβ


theorem
    eventually_freeSelectedSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreeSubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (freeSelectedSubcriticalCorrelationLengthFromMass h β) := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact
    freeSelectedSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree
      hagree h hβ


theorem
    eventually_freeSelectedSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreeSubcriticalCorrelationLengthBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (freeSelectedSubcriticalCorrelationLength h β) := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact
    freeSelectedSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree
      hagree h hβ


theorem plusSelectedSubcriticalMass_hasFreeInverseCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : PlusSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay (plusSelectedSubcriticalMass h β) :=
  free_hasInverseCorrelationLength_xAxis_of_plus_agree hagree hβ
    (plusSelectedSubcriticalMass_hasInverseCorrelationLength h hβ)


theorem
    plusSelectedSubcriticalCorrelationLengthFromMass_hasFreeCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : PlusSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
      (plusSelectedSubcriticalCorrelationLengthFromMass h β) :=
  free_hasCorrelationLength_xAxis_of_plus_agree hagree hβ
    (plusSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength h hβ)


theorem plusSelectedSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : PlusSubcriticalCorrelationLengthBridge)
    {β : ℝ} (hβ : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
      (plusSelectedSubcriticalCorrelationLength h β) :=
  free_hasCorrelationLength_xAxis_of_plus_agree hagree hβ
    (plusSelectedSubcriticalCorrelationLength_hasCorrelationLength h hβ)


theorem
    eventually_plusSelectedSubcriticalMass_hasFreeInverseCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : PlusSubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay (plusSelectedSubcriticalMass h β) := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact
    plusSelectedSubcriticalMass_hasFreeInverseCorrelationLength_of_agree
      hagree h hβ


theorem
    eventually_plusSelectedSubcriticalCorrelationLengthFromMass_hasFreeCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : PlusSubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
        (plusSelectedSubcriticalCorrelationLengthFromMass h β) := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact
    plusSelectedSubcriticalCorrelationLengthFromMass_hasFreeCorrelationLength_of_agree
      hagree h hβ


theorem
    eventually_plusSelectedSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : PlusSubcriticalCorrelationLengthBridge) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
        (plusSelectedSubcriticalCorrelationLength h β) := by
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact
    plusSelectedSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree
      hagree h hβ


theorem freeSelectedPositiveSubcriticalMass_hasPlusInverseCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreePositiveSubcriticalMassBridge)
    {β : ℝ} (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay (freeSelectedPositiveSubcriticalMass h β) :=
  plus_hasInverseCorrelationLength_xAxis_of_free_agree hagree hβc
    (freeSelectedPositiveSubcriticalMass_hasInverseCorrelationLength
      h hβpos hβc)


theorem
    freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreePositiveSubcriticalMassBridge)
    {β : ℝ} (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass h β) :=
  plus_hasCorrelationLength_xAxis_of_free_agree hagree hβc
    (freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCorrelationLength
      h hβpos hβc)


theorem
    freeSelectedPositiveSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreePositiveSubcriticalCorrelationLengthBridge)
    {β : ℝ} (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (freeSelectedPositiveSubcriticalCorrelationLength h β) :=
  plus_hasCorrelationLength_xAxis_of_free_agree hagree hβc
    (freeSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength
      h hβpos hβc)


theorem
    plusSelectedPositiveSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : PlusPositiveSubcriticalCorrelationLengthBridge)
    {β : ℝ} (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
      (plusSelectedPositiveSubcriticalCorrelationLength h β) :=
  free_hasCorrelationLength_xAxis_of_plus_agree hagree hβc
    (plusSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength
      h hβpos hβc)


theorem plusSelectedPositiveSubcriticalMass_hasFreeInverseCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : PlusPositiveSubcriticalMassBridge)
    {β : ℝ} (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay (plusSelectedPositiveSubcriticalMass h β) :=
  free_hasInverseCorrelationLength_xAxis_of_plus_agree hagree hβc
    (plusSelectedPositiveSubcriticalMass_hasInverseCorrelationLength
      h hβpos hβc)


theorem
    plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasFreeCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : PlusPositiveSubcriticalMassBridge)
    {β : ℝ} (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
      (plusSelectedPositiveSubcriticalCorrelationLengthFromMass h β) :=
  free_hasCorrelationLength_xAxis_of_plus_agree hagree hβc
    (plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCorrelationLength
      h hβpos hβc)


theorem
    eventually_freeSelectedPositiveSubcriticalMass_hasPlusInverseCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreePositiveSubcriticalMassBridge) {δ : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (freeSelectedPositiveSubcriticalMass h β) := by
  filter_upwards [eventually_mem_positiveSubcriticalWindow hδ] with β hβ
  exact
    freeSelectedPositiveSubcriticalMass_hasPlusInverseCorrelationLength_of_agree
      hagree h (beta_pos_of_mem_positiveSubcriticalWindow hδle hβ) hβ.2


theorem
    eventually_freePosSubcriticalLengthFromMass_hasPlusCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreePositiveSubcriticalMassBridge) {δ : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (freeSelectedPositiveSubcriticalCorrelationLengthFromMass h β) := by
  filter_upwards [eventually_mem_positiveSubcriticalWindow hδ] with β hβ
  exact
    freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree
      hagree h (beta_pos_of_mem_positiveSubcriticalWindow hδle hβ) hβ.2


theorem
    eventually_plusSelectedPositiveSubcriticalMass_hasFreeInverseCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : PlusPositiveSubcriticalMassBridge) {δ : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay (plusSelectedPositiveSubcriticalMass h β) := by
  filter_upwards [eventually_mem_positiveSubcriticalWindow hδ] with β hβ
  exact
    plusSelectedPositiveSubcriticalMass_hasFreeInverseCorrelationLength_of_agree
      hagree h (beta_pos_of_mem_positiveSubcriticalWindow hδle hβ) hβ.2


theorem
    eventually_plusPosSubcriticalLengthFromMass_hasFreeCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : PlusPositiveSubcriticalMassBridge) {δ : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
        (plusSelectedPositiveSubcriticalCorrelationLengthFromMass h β) := by
  filter_upwards [eventually_mem_positiveSubcriticalWindow hδ] with β hβ
  exact
    plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasFreeCorrelationLength_of_agree
      hagree h (beta_pos_of_mem_positiveSubcriticalWindow hδle hβ) hβ.2


theorem
    eventually_freeSelectedPositiveSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreePositiveSubcriticalCorrelationLengthBridge) {δ : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (freeSelectedPositiveSubcriticalCorrelationLength h β) := by
  filter_upwards [eventually_mem_positiveSubcriticalWindow hδ] with β hβ
  exact
    freeSelectedPositiveSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree
      hagree h (beta_pos_of_mem_positiveSubcriticalWindow hδle hβ) hβ.2


theorem
    eventually_plusSelectedPositiveSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : PlusPositiveSubcriticalCorrelationLengthBridge) {δ : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
        (plusSelectedPositiveSubcriticalCorrelationLength h β) := by
  filter_upwards [eventually_mem_positiveSubcriticalWindow hδ] with β hβ
  exact
    plusSelectedPositiveSubcriticalCorrelationLength_hasFreeCorrelationLength_of_agree
      hagree h (beta_pos_of_mem_positiveSubcriticalWindow hδle hβ) hβ.2


theorem plusSubcriticalMassBridge_of_exactExponential
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ A m, 0 < A ∧ 0 < m ∧ PlusXAxisExactExponentialDecay β A m) :
    PlusSubcriticalMassBridge := by
  intro β hβ
  obtain ⟨A, m, hA, hm, hG⟩ := h β hβ
  exact ⟨m, hm, plus_hasInverseCorrelationLength_xAxis_of_exactExponential hA hG⟩


theorem freeSubcriticalMassBridge_of_exactExponential
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ A m, 0 < A ∧ 0 < m ∧ FreeXAxisExactExponentialDecay β A m) :
    FreeSubcriticalMassBridge := by
  intro β hβ
  obtain ⟨A, m, hA, hm, hG⟩ := h β hβ
  exact ⟨m, hm, free_hasInverseCorrelationLength_xAxis_of_exactExponential hA hG⟩


theorem plusSubcriticalMassBridge_of_subexponentialPrefactor
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (A : ℕ → ℝ) (m : ℝ), 0 < m ∧
          PlusXAxisSubexponentialPrefactorDecay β A m) :
    PlusSubcriticalMassBridge := by
  intro β hβ
  obtain ⟨A, m, hm, hG⟩ := h β hβ
  exact ⟨m, hm, plus_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor hG⟩


theorem freeSubcriticalMassBridge_of_subexponentialPrefactor
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (A : ℕ → ℝ) (m : ℝ), 0 < m ∧
          FreeXAxisSubexponentialPrefactorDecay β A m) :
    FreeSubcriticalMassBridge := by
  intro β hβ
  obtain ⟨A, m, hm, hG⟩ := h β hβ
  exact ⟨m, hm, free_hasInverseCorrelationLength_xAxis_of_subexponentialPrefactor hG⟩


theorem plusSubcriticalMassBridge_of_twoSidedSubexponentialBounds
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧
          PlusXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
    PlusSubcriticalMassBridge := by
  intro β hβ
  obtain ⟨Alo, Ahi, m, hm, hG⟩ := h β hβ
  exact ⟨m, hm,
    plus_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds hG⟩


theorem freeSubcriticalMassBridge_of_twoSidedSubexponentialBounds
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧
          FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
    FreeSubcriticalMassBridge := by
  intro β hβ
  obtain ⟨Alo, Ahi, m, hm, hG⟩ := h β hβ
  exact ⟨m, hm,
    free_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds hG⟩


theorem plusSubcriticalMassBridge_of_fkConnectionExactExponential
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (conn : ℕ → ℝ) (A m : ℝ), 0 < A ∧ 0 < m ∧
          PlusXAxisFKConnectionAgrees β conn ∧
            FKXAxisConnectionExactExponentialDecay conn A m) :
    PlusSubcriticalMassBridge :=
  plusSubcriticalMassBridge_of_exactExponential <| by
    intro β hβ
    obtain ⟨conn, A, m, hA, hm, hcmp, hconn⟩ := h β hβ
    exact ⟨A, m, hA, hm,
      plusXAxisExactExponentialDecay_of_fkConnectionComparison hcmp hconn⟩


theorem freeSubcriticalMassBridge_of_fkConnectionExactExponential
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (conn : ℕ → ℝ) (A m : ℝ), 0 < A ∧ 0 < m ∧
          FreeXAxisFKConnectionAgrees β conn ∧
            FKXAxisConnectionExactExponentialDecay conn A m) :
    FreeSubcriticalMassBridge :=
  freeSubcriticalMassBridge_of_exactExponential <| by
    intro β hβ
    obtain ⟨conn, A, m, hA, hm, hcmp, hconn⟩ := h β hβ
    exact ⟨A, m, hA, hm,
      freeXAxisExactExponentialDecay_of_fkConnectionComparison hcmp hconn⟩


theorem plusSubcriticalMassBridge_of_fkConnectionSubexponentialPrefactor
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (conn A : ℕ → ℝ) (m : ℝ), 0 < m ∧
          PlusXAxisFKConnectionAgrees β conn ∧
            FKXAxisConnectionSubexponentialPrefactorDecay conn A m) :
    PlusSubcriticalMassBridge :=
  plusSubcriticalMassBridge_of_subexponentialPrefactor <| by
    intro β hβ
    obtain ⟨conn, A, m, hm, hcmp, hconn⟩ := h β hβ
    exact ⟨A, m, hm,
      plusXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison
        hcmp hconn⟩


theorem freeSubcriticalMassBridge_of_fkConnectionSubexponentialPrefactor
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (conn A : ℕ → ℝ) (m : ℝ), 0 < m ∧
          FreeXAxisFKConnectionAgrees β conn ∧
            FKXAxisConnectionSubexponentialPrefactorDecay conn A m) :
    FreeSubcriticalMassBridge :=
  freeSubcriticalMassBridge_of_subexponentialPrefactor <| by
    intro β hβ
    obtain ⟨conn, A, m, hm, hcmp, hconn⟩ := h β hβ
    exact ⟨A, m, hm,
      freeXAxisSubexponentialPrefactorDecay_of_fkConnectionComparison
        hcmp hconn⟩


theorem plusSubcriticalMassBridge_of_fkConnectionTwoSidedSubexponentialBounds
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (conn Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧
          PlusXAxisFKConnectionAgrees β conn ∧
            FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m) :
    PlusSubcriticalMassBridge :=
  plusSubcriticalMassBridge_of_twoSidedSubexponentialBounds <| by
    intro β hβ
    obtain ⟨conn, Alo, Ahi, m, hm, hcmp, hconn⟩ := h β hβ
    exact ⟨Alo, Ahi, m, hm,
      plusXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison
        hcmp hconn⟩


theorem freeSubcriticalMassBridge_of_fkConnectionTwoSidedSubexponentialBounds
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (conn Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧
          FreeXAxisFKConnectionAgrees β conn ∧
            FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m) :
    FreeSubcriticalMassBridge :=
  freeSubcriticalMassBridge_of_twoSidedSubexponentialBounds <| by
    intro β hβ
    obtain ⟨conn, Alo, Ahi, m, hm, hcmp, hconn⟩ := h β hβ
    exact ⟨Alo, Ahi, m, hm,
      freeXAxisTwoSidedSubexponentialBounds_of_fkConnectionComparison
        hcmp hconn⟩


theorem plusSubcriticalMassBridge_of_free_and_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeSubcriticalMassBridge) :
    PlusSubcriticalMassBridge := by
  intro β hβ
  obtain ⟨m, hm, hmass⟩ := hfree β hβ
  exact ⟨m, hm,
    plus_hasInverseCorrelationLength_xAxis_of_free_agree hagree hβ hmass⟩


theorem freeSubcriticalMassBridge_of_plus_and_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hplus : PlusSubcriticalMassBridge) :
    FreeSubcriticalMassBridge := by
  intro β hβ
  obtain ⟨m, hm, hmass⟩ := hplus β hβ
  exact ⟨m, hm,
    free_hasInverseCorrelationLength_xAxis_of_plus_agree hagree hβ hmass⟩


theorem subcriticalMassBridge_plus_free_agree_iff
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) :
    PlusSubcriticalMassBridge ↔ FreeSubcriticalMassBridge :=
  ⟨freeSubcriticalMassBridge_of_plus_and_agree hagree,
    plusSubcriticalMassBridge_of_free_and_agree hagree⟩


theorem plusPositiveSubcriticalMassBridge_of_free_and_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreePositiveSubcriticalMassBridge) :
    PlusPositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨m, hm, hmass⟩ := hfree β hβpos hβc
  exact ⟨m, hm,
    plus_hasInverseCorrelationLength_xAxis_of_free_agree hagree hβc hmass⟩


theorem freePositiveSubcriticalMassBridge_of_plus_and_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hplus : PlusPositiveSubcriticalMassBridge) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨m, hm, hmass⟩ := hplus β hβpos hβc
  exact ⟨m, hm,
    free_hasInverseCorrelationLength_xAxis_of_plus_agree hagree hβc hmass⟩


theorem positiveSubcriticalMassBridge_plus_free_agree_iff
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) :
    PlusPositiveSubcriticalMassBridge ↔ FreePositiveSubcriticalMassBridge :=
  ⟨freePositiveSubcriticalMassBridge_of_plus_and_agree hagree,
    plusPositiveSubcriticalMassBridge_of_free_and_agree hagree⟩


theorem plusSubcriticalCorrelationLengthBridge_of_massBridge
    (hmass : PlusSubcriticalMassBridge) :
    PlusSubcriticalCorrelationLengthBridge := by
  intro β hβ
  obtain ⟨m, hm, hlen⟩ := hmass β hβ
  exact ⟨m⁻¹, inv_pos.mpr hm, hlen.hasCorrelationLength_inv hm⟩


theorem freeSubcriticalCorrelationLengthBridge_of_massBridge
    (hmass : FreeSubcriticalMassBridge) :
    FreeSubcriticalCorrelationLengthBridge := by
  intro β hβ
  obtain ⟨m, hm, hlen⟩ := hmass β hβ
  exact ⟨m⁻¹, inv_pos.mpr hm, hlen.hasCorrelationLength_inv hm⟩


theorem plusSubcriticalCorrelationLengthBridge_of_exactExponential
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ A m, 0 < A ∧ 0 < m ∧ PlusXAxisExactExponentialDecay β A m) :
    PlusSubcriticalCorrelationLengthBridge :=
  plusSubcriticalCorrelationLengthBridge_of_massBridge
    (plusSubcriticalMassBridge_of_exactExponential h)


theorem freeSubcriticalCorrelationLengthBridge_of_exactExponential
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ A m, 0 < A ∧ 0 < m ∧ FreeXAxisExactExponentialDecay β A m) :
    FreeSubcriticalCorrelationLengthBridge :=
  freeSubcriticalCorrelationLengthBridge_of_massBridge
    (freeSubcriticalMassBridge_of_exactExponential h)


theorem plusSubcriticalCorrelationLengthBridge_of_subexponentialPrefactor
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (A : ℕ → ℝ) (m : ℝ), 0 < m ∧
          PlusXAxisSubexponentialPrefactorDecay β A m) :
    PlusSubcriticalCorrelationLengthBridge :=
  plusSubcriticalCorrelationLengthBridge_of_massBridge
    (plusSubcriticalMassBridge_of_subexponentialPrefactor h)


theorem freeSubcriticalCorrelationLengthBridge_of_subexponentialPrefactor
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (A : ℕ → ℝ) (m : ℝ), 0 < m ∧
          FreeXAxisSubexponentialPrefactorDecay β A m) :
    FreeSubcriticalCorrelationLengthBridge :=
  freeSubcriticalCorrelationLengthBridge_of_massBridge
    (freeSubcriticalMassBridge_of_subexponentialPrefactor h)


theorem plusSubcriticalCorrelationLengthBridge_of_twoSidedSubexponentialBounds
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧
          PlusXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
    PlusSubcriticalCorrelationLengthBridge :=
  plusSubcriticalCorrelationLengthBridge_of_massBridge
    (plusSubcriticalMassBridge_of_twoSidedSubexponentialBounds h)


theorem freeSubcriticalCorrelationLengthBridge_of_twoSidedSubexponentialBounds
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧
          FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi m) :
    FreeSubcriticalCorrelationLengthBridge :=
  freeSubcriticalCorrelationLengthBridge_of_massBridge
    (freeSubcriticalMassBridge_of_twoSidedSubexponentialBounds h)


theorem plusSubcriticalCorrelationLengthBridge_of_fkConnectionExactExponential
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (conn : ℕ → ℝ) (A m : ℝ), 0 < A ∧ 0 < m ∧
          PlusXAxisFKConnectionAgrees β conn ∧
            FKXAxisConnectionExactExponentialDecay conn A m) :
    PlusSubcriticalCorrelationLengthBridge :=
  plusSubcriticalCorrelationLengthBridge_of_massBridge
    (plusSubcriticalMassBridge_of_fkConnectionExactExponential h)


theorem freeSubcriticalCorrelationLengthBridge_of_fkConnectionExactExponential
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (conn : ℕ → ℝ) (A m : ℝ), 0 < A ∧ 0 < m ∧
          FreeXAxisFKConnectionAgrees β conn ∧
            FKXAxisConnectionExactExponentialDecay conn A m) :
    FreeSubcriticalCorrelationLengthBridge :=
  freeSubcriticalCorrelationLengthBridge_of_massBridge
    (freeSubcriticalMassBridge_of_fkConnectionExactExponential h)


theorem
    plusSubcriticalCorrelationLengthBridge_of_fkConnectionSubexponentialPrefactor
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (conn A : ℕ → ℝ) (m : ℝ), 0 < m ∧
          PlusXAxisFKConnectionAgrees β conn ∧
            FKXAxisConnectionSubexponentialPrefactorDecay conn A m) :
    PlusSubcriticalCorrelationLengthBridge :=
  plusSubcriticalCorrelationLengthBridge_of_massBridge
    (plusSubcriticalMassBridge_of_fkConnectionSubexponentialPrefactor h)


theorem
    freeSubcriticalCorrelationLengthBridge_of_fkConnectionSubexponentialPrefactor
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (conn A : ℕ → ℝ) (m : ℝ), 0 < m ∧
          FreeXAxisFKConnectionAgrees β conn ∧
            FKXAxisConnectionSubexponentialPrefactorDecay conn A m) :
    FreeSubcriticalCorrelationLengthBridge :=
  freeSubcriticalCorrelationLengthBridge_of_massBridge
    (freeSubcriticalMassBridge_of_fkConnectionSubexponentialPrefactor h)


theorem
    plusSubcriticalCorrelationLengthBridge_of_fkConnectionTwoSidedSubexponentialBounds
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (conn Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧
          PlusXAxisFKConnectionAgrees β conn ∧
            FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m) :
    PlusSubcriticalCorrelationLengthBridge :=
  plusSubcriticalCorrelationLengthBridge_of_massBridge
    (plusSubcriticalMassBridge_of_fkConnectionTwoSidedSubexponentialBounds h)


theorem
    freeSubcriticalCorrelationLengthBridge_of_fkConnectionTwoSidedSubexponentialBounds
    (h :
      ∀ β, β < Ising.betaC 3 →
        ∃ (conn Alo Ahi : ℕ → ℝ) (m : ℝ), 0 < m ∧
          FreeXAxisFKConnectionAgrees β conn ∧
            FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m) :
    FreeSubcriticalCorrelationLengthBridge :=
  freeSubcriticalCorrelationLengthBridge_of_massBridge
    (freeSubcriticalMassBridge_of_fkConnectionTwoSidedSubexponentialBounds h)


theorem plusSubcriticalCorrelationLengthBridge_of_free_and_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeSubcriticalCorrelationLengthBridge) :
    PlusSubcriticalCorrelationLengthBridge := by
  intro β hβ
  obtain ⟨ξ, hξ, hcorr⟩ := hfree β hβ
  exact ⟨ξ, hξ, plus_hasCorrelationLength_xAxis_of_free_agree hagree hβ hcorr⟩


theorem freeSubcriticalCorrelationLengthBridge_of_plus_and_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hplus : PlusSubcriticalCorrelationLengthBridge) :
    FreeSubcriticalCorrelationLengthBridge := by
  intro β hβ
  obtain ⟨ξ, hξ, hcorr⟩ := hplus β hβ
  exact ⟨ξ, hξ, free_hasCorrelationLength_xAxis_of_plus_agree hagree hβ hcorr⟩


theorem subcriticalCorrelationLengthBridge_plus_free_agree_iff
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) :
    PlusSubcriticalCorrelationLengthBridge ↔
      FreeSubcriticalCorrelationLengthBridge :=
  ⟨freeSubcriticalCorrelationLengthBridge_of_plus_and_agree hagree,
    plusSubcriticalCorrelationLengthBridge_of_free_and_agree hagree⟩


theorem plusPositiveSubcriticalCorrelationLengthBridge_of_free_and_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreePositiveSubcriticalCorrelationLengthBridge) :
    PlusPositiveSubcriticalCorrelationLengthBridge := by
  intro β hβpos hβc
  obtain ⟨ξ, hξ, hcorr⟩ := hfree β hβpos hβc
  exact ⟨ξ, hξ, plus_hasCorrelationLength_xAxis_of_free_agree
    hagree hβc hcorr⟩


theorem freePositiveSubcriticalCorrelationLengthBridge_of_plus_and_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hplus : PlusPositiveSubcriticalCorrelationLengthBridge) :
    FreePositiveSubcriticalCorrelationLengthBridge := by
  intro β hβpos hβc
  obtain ⟨ξ, hξ, hcorr⟩ := hplus β hβpos hβc
  exact ⟨ξ, hξ, free_hasCorrelationLength_xAxis_of_plus_agree
    hagree hβc hcorr⟩


theorem positiveSubcriticalCorrelationLengthBridge_plus_free_agree_iff
    (hagree : PlusFreeTwoPointAgreeBelowBetaC) :
    PlusPositiveSubcriticalCorrelationLengthBridge ↔
      FreePositiveSubcriticalCorrelationLengthBridge :=
  ⟨freePositiveSubcriticalCorrelationLengthBridge_of_plus_and_agree hagree,
    plusPositiveSubcriticalCorrelationLengthBridge_of_free_and_agree hagree⟩


theorem plusSubcriticalCorrelationLengthBridge_of_freeMassBridge_and_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreeSubcriticalMassBridge) :
    PlusSubcriticalCorrelationLengthBridge :=
  plusSubcriticalCorrelationLengthBridge_of_massBridge
    (plusSubcriticalMassBridge_of_free_and_agree hagree hfree)


theorem freeSubcriticalCorrelationLengthBridge_of_plusMassBridge_and_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hplus : PlusSubcriticalMassBridge) :
    FreeSubcriticalCorrelationLengthBridge :=
  freeSubcriticalCorrelationLengthBridge_of_massBridge
    (freeSubcriticalMassBridge_of_plus_and_agree hagree hplus)


theorem plusPositiveSubcriticalCorrelationLengthBridge_of_freeMassBridge_and_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hfree : FreePositiveSubcriticalMassBridge) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPositiveSubcriticalMassBridge_of_free_and_agree hagree hfree)


theorem freePositiveSubcriticalCorrelationLengthBridge_of_plusMassBridge_and_agree
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hplus : PlusPositiveSubcriticalMassBridge) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePositiveSubcriticalMassBridge_of_plus_and_agree hagree hplus)

end Exact3D
end StatMech
