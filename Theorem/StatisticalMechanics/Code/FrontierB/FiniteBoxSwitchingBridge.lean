/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityDiagonal.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteBoxSwitchingBridge
open MeasureTheory Set SimpleGraph
open scoped ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Lattice Percolation


@[simp] theorem edgeCurrentOfCurrent_ofEdgeFun
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : EdgeCurrent G) :
    edgeCurrentOfCurrent G (ofEdgeFun G m) = m := by
  funext e
  simp [edgeCurrentOfCurrent, ofEdgeFun, e.2]


end StatMech.FrontierB
