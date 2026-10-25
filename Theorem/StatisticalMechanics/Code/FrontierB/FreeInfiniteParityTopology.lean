/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityNoEscape.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FreeParityErrorReduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open ConfigSpace FK Lattice Percolation

variable {d : Nat}

theorem isOpen_connectedEvent (x y : Site d) :
    IsOpen {omega : ConfigSpace (Sym2 (Site d)) | Connected d omega x y} := by
  rw [<- iUnion_boxConnectionEvent x y]
  exact isOpen_iUnion fun n => (isClopen_boxConnectionEvent n x y).isOpen


end StatMech.FrontierB
