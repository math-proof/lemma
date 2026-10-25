/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG


namespace StatMech

namespace Exact3D

namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type}


noncomputable def fixedPointData
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (thermal : ℝ) (hthermal : 1 < thermal) :
    RGFixedPointData C.hamiltonian (C.rgMap scale) where
  fixedPoint := C.fixedPoint
  fixedPoint_eq := C.fixedPoint_isFixed
  thermalEigenvalue := thermal
  thermal_gt_one := hthermal


noncomputable def certificate {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) : RGCertificate M where
  H := C.hamiltonian
  R := C.rgMap scale
  fixedPointData := C.fixedPointData scale thermal hthermal


end FinitePlusTailClosedBallContractionCertificate
end Exact3D
end StatMech
