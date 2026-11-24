module
public import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
public import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableWitnessPackage.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]

variable {M : CriticalModel ι}


abbrev State (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M) :
    Type :=
  W.toWitnessPackage.State


end InfiniteTailTableWitnessPackage
end Exact3D
end StatMech
