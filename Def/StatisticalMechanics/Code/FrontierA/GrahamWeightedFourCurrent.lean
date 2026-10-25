/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFourCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
import Theorem.StatisticalMechanics.Code.Walls.ghggrahamclose
open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]


def grahamAllThreeConnected (G : SimpleGraph V) (m : Current V)
    (i j k l : V) : Prop :=
  CurrentConnected G m i j ∧ CurrentConnected G m i k ∧
    CurrentConnected G m i l


end StatMech.FrontierA
