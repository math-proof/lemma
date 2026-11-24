module
public import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic
public import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummabilityExample.Part2
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace InfiniteTailSummabilityExample

open TailSummability

noncomputable section

def maskedGeometricHalfTailWeight (n : ℕ) : ℝ :=
  if n ∈ ({0} : Finset ℕ) then 0 else geometricHalfTailWeight n


end
end InfiniteTailSummabilityExample
end Exact3D
end StatMech
