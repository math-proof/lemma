/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailCone.Part4
import Abbrev.StatisticalMechanics.Code.Exact3D.FinitePlusTailRG


namespace StatMech

namespace Exact3D

namespace FinitePlusTailHyperbolicSplitting

variable {n : ℕ} {α : Type}


noncomputable def rgMap (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) : BlockSpinMap H.hamiltonian where
  scale := scale
  map := H.step


noncomputable def fixedPointData
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) : RGFixedPointData H.hamiltonian (H.rgMap scale) where
  fixedPoint := origin
  fixedPoint_eq := H.step_origin
  thermalEigenvalue := H.thermal
  thermal_gt_one := H.thermal_gt_one


noncomputable def certificate {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) : RGCertificate M where
  H := H.hamiltonian
  R := H.rgMap scale
  fixedPointData := H.fixedPointData scale

end FinitePlusTailHyperbolicSplitting
end Exact3D
end StatMech
