/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailRG
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG.Part3


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockRGPackage

variable {n : ℕ} {α : Type}


noncomputable def hyperbolicSplitting
    (P : FinitePlusTailBlockRGPackage n α) :
    FinitePlusTailHyperbolicSplitting n α where
  thermal := P.thermal
  thermal_gt_one := P.thermal_gt_one
  stable := P.stableCertificate
  stable_origin := by
    simpa [stableCertificate] using P.origin_fixed
  stable_dominated := by
    simpa [stableCertificate] using P.stable_dominated


end FinitePlusTailBlockRGPackage
end Exact3D
end StatMech
