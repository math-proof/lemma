/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


@[simp] theorem certificate_scale_eq
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.scale = W.scale :=
  rfl


@[simp] theorem certificate_thermalEigenvalue_eq
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.thermalEigenvalue = W.thermal :=
  rfl


@[simp] theorem certificate_fixedPoint_eq
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.fixedPointData.fixedPoint = W.fixedPoint :=
  rfl


theorem certificate_predictedExponent_eq
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.certificate.predictedExponent = predictedNu W.scale W.thermal :=
  rfl


end InfiniteTailTableWitnessPackage
end Exact3D
end StatMech
