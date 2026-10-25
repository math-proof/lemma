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
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredWeakLimitIdentification.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def boxOpenToExtendWiredOpenHom
    (d n : Nat) (omega : ConfigSpace (Sym2 (boxVerts d n))) :
    openSub (boxGraph d n) omega →g
      openSubgraph d (extendWiredEdge d n omega) where
  toFun := Subtype.val
  map_rel' := fun {_ _} h => boxOpen_adj_extendWiredEdge omega h

end StatMech.FK
