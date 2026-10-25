/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityDiagonal.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoxSwitchingBridge
open MeasureTheory Set SimpleGraph
open scoped ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Lattice Percolation


noncomputable def finiteBoxCurrentTrace (d n : ℕ)
    (m : Current (StatMech.FK.boxVerts d n)) :
    ConfigSpace (Sym2 (Site d)) :=
  currentTrace (extendBoxCurrent d n
    (edgeCurrentOfCurrent (StatMech.FK.boxGraph d n) m))


end StatMech.FrontierB
