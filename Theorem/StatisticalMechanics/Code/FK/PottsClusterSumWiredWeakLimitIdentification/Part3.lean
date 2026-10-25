/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part6
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.FreeDLRExtreme
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredWeakLimitIdentification.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem boxOpen_adj_extendWiredEdge
    {d n : Nat} (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {x y : boxVerts d n}
    (hxy : (openSub (boxGraph d n) omega).Adj x y) :
    (openSubgraph d (extendWiredEdge d n omega)).Adj (x : Site d) (y : Site d) := by
  rw [openSub_adj] at hxy
  rw [openSubgraph_adj]
  constructor
  · simpa [boxGraph] using hxy.1
  · have heq : s((x : Site d), (y : Site d)) =
        edgeIncl d n s(x, y) := by
      simp [edgeIncl]
    rw [heq, extendWiredEdge_eq_of_range]
    exact hxy.2

end StatMech.FK
