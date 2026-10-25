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
import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteParityTopology
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open ConfigSpace FK Lattice Percolation

variable {d : Nat}

noncomputable def finiteClusterNeighborhood
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hfin : (cluster d omega x).Finite) : Finset (Site d) := by
  classical
  let K := hfin.toFinset
  exact K ∪ K.biUnion (fun z => (hypercubicLattice d).neighborFinset z)

end StatMech.FrontierB
