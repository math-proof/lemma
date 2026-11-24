module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.FK.PressureDiff
public import Theorem.StatisticalMechanics.Code.FK.DlrSandwich
public import Theorem.StatisticalMechanics.Code.FK.Uniqueness
public import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
public import Theorem.StatisticalMechanics.Code.FK.FKUniquenessFull
open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessFull.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open ConfigSpace


section InfiniteVolume

open StatMech.Lattice


def fkEdgeOpenEvent {E : Type*} (e : E) : Set (ConfigSpace E) := {ω | ω e = true}


end InfiniteVolume
end FK
end StatMech
