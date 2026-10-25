/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge.Part2


namespace StatMech

namespace Exact3D

namespace IsingRGCoordinateScaffold

variable {C : RGCertificate Ising3DModel}


theorem length_covariance_maps_interval
    (S : IsingRGCoordinateScaffold C)
    (hcov : S.LengthCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    S.renormalizedBeta β ∈ S.leftCriticalInterval :=
  (hcov β hβ).1


theorem length_covariance_lattice_scale
    (S : IsingRGCoordinateScaffold C)
    (hcov : S.LengthCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    S.correlationLength (S.renormalizedBeta β) =
      S.correlationLength β / S.latticeRG.kernel.scale.toReal :=
  (hcov β hβ).2


theorem length_covariance_certificate_scale
    (S : IsingRGCoordinateScaffold C)
    (hcov : S.LengthCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    S.correlationLength (S.renormalizedBeta β) =
      S.correlationLength β / C.scale.toReal := by
  have h := (hcov β hβ).2
  rw [S.latticeRG_kernel_scale_toReal_eq_certificate] at h
  exact h


theorem coordinate_rg_covariance
    (S : IsingRGCoordinateScaffold C)
    (hcov : S.CoordinateRGCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    C.R.map (S.coordinate β) = S.coordinate (S.renormalizedBeta β) :=
  hcov β hβ

end IsingRGCoordinateScaffold
end Exact3D
end StatMech
