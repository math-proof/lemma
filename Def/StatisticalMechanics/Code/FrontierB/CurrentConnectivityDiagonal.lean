/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityApproximation.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open Lattice

variable {d : ℕ}


def currentPairTraceBoxGate
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (n : ℕ) (x y : Site d) :
    Set (InfiniteCurrentConfig (Sym2 (Site d)) ×
      InfiniteCurrentConfig (Sym2 (Site d))) :=
  superposedCurrentTrace ⁻¹' (Q ∩ boxConnectionEvent n x y)


def currentPairTraceConnectionGate
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (x y : Site d) :
    Set (InfiniteCurrentConfig (Sym2 (Site d)) ×
      InfiniteCurrentConfig (Sym2 (Site d))) :=
  superposedCurrentTrace ⁻¹' (Q ∩ {omega | Connected d omega x y})

end StatMech.FrontierB
