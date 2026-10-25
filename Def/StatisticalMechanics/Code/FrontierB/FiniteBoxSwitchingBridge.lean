/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityDiagonal.Part2
open MeasureTheory Set SimpleGraph
open scoped ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Lattice Percolation


def edgeCurrentOfCurrent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : Current V) : EdgeCurrent G :=
  fun e => m e.1

end StatMech.FrontierB
