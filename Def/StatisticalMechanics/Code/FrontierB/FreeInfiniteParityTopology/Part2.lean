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
import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteParityTopology.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open ConfigSpace FK Lattice Percolation

variable {d : Nat}

noncomputable def markReachableCount
    {V : Type*} (G : SimpleGraph V) (omega : ConfigSpace (Sym2 V))
    (A : Finset V) (x : V) : Nat := by
  classical
  exact (A.filter fun y => (openSub G omega).Reachable x y).card

end StatMech.FrontierB
