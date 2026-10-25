/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
import Abbrev.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


noncomputable def hamiltonian
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    EffectiveHamiltonian :=
  W.toWitnessPackage.hamiltonian


noncomputable def rgMap
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    BlockSpinMap W.hamiltonian :=
  W.toWitnessPackage.rgMap


noncomputable def fixedPoint
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    W.State :=
  W.toWitnessPackage.fixedPoint


end InfiniteTailTableWitnessPackage
end Exact3D
end StatMech
