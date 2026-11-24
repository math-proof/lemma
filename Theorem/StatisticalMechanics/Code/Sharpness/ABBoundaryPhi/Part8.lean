module
public import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryProfile.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part13
public import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
public import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
public import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
public import Mathlib.Data.Finset.Preimage
public import Def.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part7
open Filter Finset Set SimpleGraph Topology
open scoped NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation


@[simp] theorem abbPairToSite_some_some (d n : Nat) (x y : sctBox d n) :
    abbPairToSite d n (some x, some y) = ((x : Site d), (y : Site d)) := rfl


end Sharpness
end StatMech
