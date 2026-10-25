/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteLocalSwitching.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open Lattice Percolation

variable {d : ℕ}


def boxConnectionEvent (n : ℕ) (x y : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  withinConnEvent d (box d n) x y


end StatMech.FrontierB
