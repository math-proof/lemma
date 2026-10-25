/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


noncomputable def fixedPointData
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    RGFixedPointData W.hamiltonian W.rgMap :=
  W.toWitnessPackage.fixedPointData


noncomputable def certificate
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    RGCertificate M :=
  W.toWitnessPackage.certificate


end InfiniteTailTableWitnessPackage
end Exact3D
end StatMech
