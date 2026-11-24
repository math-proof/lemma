module
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
public import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
public import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction
open scoped BigOperators ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace SummableTail

variable {α : Type*}


instance : Zero (SummableTail α) :=
  ⟨zero⟩

end SummableTail
end Exact3D
end StatMech
