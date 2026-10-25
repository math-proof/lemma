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
import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteParityTopology.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open ConfigSpace FK Lattice Percolation

variable {d : Nat}

noncomputable def connectivityStableNeighborhood
    (omega : ConfigSpace (Sym2 (Site d))) (A : Finset (Site d)) :
    Set (ConfigSpace (Sym2 (Site d))) := by
  classical
  exact ⋂ x ∈ A, ⋂ y ∈ A,
    if Lattice.Connected d omega x y then
      {eta | Lattice.Connected d eta x y}
    else
      interior {eta | Lattice.Connected d eta x y}ᶜ

end StatMech.FrontierB
