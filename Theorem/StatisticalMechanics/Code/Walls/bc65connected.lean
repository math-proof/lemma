/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc64coarseembed.Part5
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Walls.bc65connected
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc65_connectedCoarseForest_iff_armEmbedding (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bc65_ConnectedCoarseForest ω L R ↔ bc63_CoarseArmEmbedding ω L R :=
  Iff.rfl


theorem bc65_coarseArmEmbedding_of_connectedForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc65_ConnectedCoarseForest ω L R) : bc63_CoarseArmEmbedding ω L R :=
  (bc65_connectedCoarseForest_iff_armEmbedding ω L R).mp h


theorem bc65_coarseTcount_le_boundary_of_connectedForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc65_ConnectedCoarseForest ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc63_coarseTcount_le_boundary_of_armEmbedding ω L R
    (bc65_coarseArmEmbedding_of_connectedForest ω L R h)


theorem bc65_connected_leaf_count {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (univ.filter (fun v => G.degree v = 1)).card :=
  flc2_forest_internal_le_leaves G hacyc hmin


end StatMech.Walls
