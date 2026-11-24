module
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
public import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
public import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part2
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}


@[simp] theorem rgMap_scale
    (W : InfiniteTailWitnessPackage (α := α) M) :
    W.rgMap.scale = W.scale :=
  rfl


end InfiniteTailWitnessPackage
end Exact3D
end StatMech
