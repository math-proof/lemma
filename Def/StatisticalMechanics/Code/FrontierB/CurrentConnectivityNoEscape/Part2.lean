/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityDiagonal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneErgodic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityNoEscape
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open Lattice Percolation

variable {d : ℕ}


noncomputable def twoArmDisconnectedTraceEvent (m : ℕ) (x y : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  (traceBoundaryConnectionEvent m x ∩ traceBoundaryConnectionEvent m y) \
    boxConnectionEvent m x y

end StatMech.FrontierB
