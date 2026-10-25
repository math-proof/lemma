/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge.Part5


namespace StatMech

namespace Exact3D

namespace IsingMassRGCoordinateScaffold

variable {C : RGCertificate Ising3DModel}


theorem mass_covariance_maps_interval
    (S : IsingMassRGCoordinateScaffold C)
    (hcov : S.MassCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    S.renormalizedBeta β ∈ S.leftCriticalInterval :=
  (hcov β hβ).1


theorem mass_covariance_lattice_scale
    (S : IsingMassRGCoordinateScaffold C)
    (hcov : S.MassCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    S.mass (S.renormalizedBeta β) =
      S.latticeRG.kernel.scale.toReal * S.mass β :=
  (hcov β hβ).2


theorem mass_covariance_certificate_scale
    (S : IsingMassRGCoordinateScaffold C)
    (hcov : S.MassCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    S.mass (S.renormalizedBeta β) = C.scale.toReal * S.mass β := by
  have h := (hcov β hβ).2
  rw [S.latticeRG_kernel_scale_toReal_eq_certificate] at h
  exact h


theorem coordinate_rg_covariance
    (S : IsingMassRGCoordinateScaffold C)
    (hcov : S.CoordinateRGCovariance) {β : ℝ}
    (hβ : β ∈ S.leftCriticalInterval) :
    C.R.map (S.coordinate β) = S.coordinate (S.renormalizedBeta β) :=
  hcov β hβ

end IsingMassRGCoordinateScaffold
end Exact3D
end StatMech
