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
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityApproximation
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open Lattice Percolation

variable {d : ℕ}


def currentPairBoxConnectionEvent (n : ℕ) (x y : Site d) :
    Set (InfiniteCurrentConfig (Sym2 (Site d)) ×
      InfiniteCurrentConfig (Sym2 (Site d))) :=
  superposedCurrentTrace ⁻¹' boxConnectionEvent n x y


def currentPairConnectionEvent (x y : Site d) :
    Set (InfiniteCurrentConfig (Sym2 (Site d)) ×
      InfiniteCurrentConfig (Sym2 (Site d))) :=
  superposedCurrentTrace ⁻¹' {omega | Connected d omega x y}

end StatMech.FrontierB
