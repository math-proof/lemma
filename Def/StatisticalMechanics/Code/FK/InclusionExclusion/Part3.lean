module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
public import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion.Part2
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


def cyl (S : Finset E) (ψ : ConfigSpace E) : Set (ConfigSpace E) :=
  {ω | ∀ e ∈ S, ω e = ψ e}


end FK
end StatMech
