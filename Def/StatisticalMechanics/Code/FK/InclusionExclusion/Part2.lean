module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
public import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion
open StatMech ConfigSpace
open scoped BigOperators Pointwise


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

variable {E : Type*}


def SignedIncreasingCombo (f : ConfigSpace E → ℝ) : Prop :=
  f ∈ Submodule.span ℝ (incrIndicators E)


end FK
end StatMech
