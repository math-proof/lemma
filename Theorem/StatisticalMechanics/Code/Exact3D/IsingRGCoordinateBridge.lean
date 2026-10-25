/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge


namespace StatMech

namespace Exact3D

namespace IsingRGCoordinateScaffold

variable {C : RGCertificate Ising3DModel}


@[simp] theorem mem_leftCriticalInterval
    (S : IsingRGCoordinateScaffold C) {β : ℝ} :
    β ∈ S.leftCriticalInterval ↔
      β ∈ Set.Ioo (Ising.betaC 3 - S.δ) (Ising.betaC 3) :=
  Iff.rfl


theorem leftCriticalInterval_subset_Iio
    (S : IsingRGCoordinateScaffold C) :
    S.leftCriticalInterval ⊆ Set.Iio (Ising.betaC 3) := by
  intro β hβ
  exact hβ.2


theorem betaC_sub_pos_of_mem_leftCriticalInterval
    (S : IsingRGCoordinateScaffold C) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    0 < Ising.betaC 3 - β :=
  sub_pos.mpr hβ.2


theorem betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (S : IsingRGCoordinateScaffold C) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    Ising.betaC 3 - β < S.δ := by
  linarith [hβ.1]


theorem eventually_mem_leftCriticalInterval
    (S : IsingRGCoordinateScaffold C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ S.leftCriticalInterval := by
  filter_upwards
    [Ioo_mem_nhdsLT (show Ising.betaC 3 - S.δ < Ising.betaC 3 by
      linarith [S.δ_pos])] with β hβ
  exact hβ


theorem eventually_betaC_sub_pos
    (S : IsingRGCoordinateScaffold C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β := by
  filter_upwards [S.eventually_mem_leftCriticalInterval] with β hβ
  exact S.betaC_sub_pos_of_mem_leftCriticalInterval hβ


theorem eventually_betaC_sub_lt_delta
    (S : IsingRGCoordinateScaffold C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < S.δ := by
  filter_upwards [S.eventually_mem_leftCriticalInterval] with β hβ
  exact S.betaC_sub_lt_delta_of_mem_leftCriticalInterval hβ

@[simp] theorem latticeRG_kernel_scale_eq_certificate
    (S : IsingRGCoordinateScaffold C) :
    S.latticeRG.kernel.scale = C.scale :=
  S.scale_match

theorem latticeRG_R_scale_eq_certificate
    (S : IsingRGCoordinateScaffold C) :
    S.latticeRG.R.scale = C.scale :=
  S.latticeRG.R_scale_eq_kernel_scale.trans S.scale_match

@[simp] theorem latticeRG_kernel_scale_toReal_eq_certificate
    (S : IsingRGCoordinateScaffold C) :
    S.latticeRG.kernel.scale.toReal = C.scale.toReal := by
  exact congrArg BlockScale.toReal S.latticeRG_kernel_scale_eq_certificate

theorem latticeRG_R_scale_toReal_eq_certificate
    (S : IsingRGCoordinateScaffold C) :
    S.latticeRG.R.scale.toReal = C.scale.toReal := by
  exact congrArg BlockScale.toReal S.latticeRG_R_scale_eq_certificate


end IsingRGCoordinateScaffold
end Exact3D
end StatMech
