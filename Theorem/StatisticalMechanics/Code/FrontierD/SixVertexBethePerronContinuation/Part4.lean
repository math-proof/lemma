/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part4
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexNoAdjacentTransferInfinity_nonneg (N n : Nat)
    (x y : SixVertexNoAdjacentSector N n) :
    0 ≤ sixVertexNoAdjacentTransferInfinity N n x y :=
  sixVertexSectorTransferInfinity_nonneg N n x.1 y.1

theorem sixVertexNoAdjacentTransferInfinity_symmetric (N n : Nat)
    (x y : SixVertexNoAdjacentSector N n) :
    sixVertexNoAdjacentTransferInfinity N n x y =
      sixVertexNoAdjacentTransferInfinity N n y x :=
  sixVertexSectorTransferInfinity_symmetric N n x.1 y.1


theorem sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_left
    {N n : Nat} {x : SixVertexSector N n}
    (hx : ¬ SixVertexSectorNoAdjacent x) (y : SixVertexSector N n) :
    sixVertexSectorTransferInfinity N n x y = 0 := by
  rw [sixVertexSectorTransferInfinity_apply]
  split_ifs with h
  · exact False.elim (hx (sixVertexInfinityGraph_adj_noAdjacent h).1)
  · rfl

theorem sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_right
    {N n : Nat} (x : SixVertexSector N n) {y : SixVertexSector N n}
    (hy : ¬ SixVertexSectorNoAdjacent y) :
    sixVertexSectorTransferInfinity N n x y = 0 := by
  rw [sixVertexSectorTransferInfinity_symmetric]
  exact sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_left hy x


end
end StatMech.FrontierD
