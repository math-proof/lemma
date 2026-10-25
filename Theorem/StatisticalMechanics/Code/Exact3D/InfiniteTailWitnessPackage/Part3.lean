/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part4
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


@[simp] theorem certificate_scale_eq
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.scale = W.scale :=
  rfl


@[simp] theorem certificate_thermalEigenvalue_eq
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.thermalEigenvalue = W.thermal :=
  rfl


@[simp] theorem certificate_fixedPoint_eq
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.fixedPointData.fixedPoint = W.fixedPoint :=
  rfl


theorem certificate_predictedExponent_eq
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.certificate.predictedExponent = predictedNu W.scale W.thermal :=
  rfl


end InfiniteTailWitnessPackage
end Exact3D
end StatMech
