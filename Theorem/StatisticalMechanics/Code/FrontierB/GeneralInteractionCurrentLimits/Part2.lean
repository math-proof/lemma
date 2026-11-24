module
public import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
public import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentCompactness
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part3
open Filter MeasureTheory Set Topology
open scoped ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Sharpness Lattice


@[simp] theorem mem_interactionBoxVertices {d n : Nat} {x : Site d} :
    x ∈ interactionBoxVertices d n ↔ x ∈ box d n := by
  simp [interactionBoxVertices]


end StatMech.FrontierB
