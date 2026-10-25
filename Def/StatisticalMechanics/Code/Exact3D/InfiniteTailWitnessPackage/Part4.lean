/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


noncomputable def fixedPointData
    (W : InfiniteTailWitnessPackage (α := α) M) :
    RGFixedPointData W.hamiltonian W.rgMap where
  fixedPoint := W.fixedPoint
  fixedPoint_eq := W.fixedPoint_eq
  thermalEigenvalue := W.thermal
  thermal_gt_one := W.thermal_gt_one


noncomputable def certificate
    (W : InfiniteTailWitnessPackage (α := α) M) :
    RGCertificate M where
  H := W.hamiltonian
  R := W.rgMap
  fixedPointData := W.fixedPointData


end InfiniteTailWitnessPackage
end Exact3D
end StatMech
