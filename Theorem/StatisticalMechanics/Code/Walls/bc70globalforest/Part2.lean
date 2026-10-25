/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc69count.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Walls.bc70globalforest.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc70_spanningForest_acyclic (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) :
    (bc70_spanningForest ω R).IsAcyclic :=
  osf_spanForest_acyclic (bc70_Gn_clusterGraph ω R)


theorem bc70_spanningForest_le (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) :
    bc70_spanningForest ω R ≤ bc70_Gn_clusterGraph ω R :=
  osf_spanForest_le (bc70_Gn_clusterGraph ω R)


theorem bc70_spanningForest_reachable_of (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ)
    {a b : (↑(box d R) : Type)} (h : (bc70_Gn_clusterGraph ω R).Reachable a b) :
    (bc70_spanningForest ω R).Reachable a b :=
  osf_spanForest_reachable_of (bc70_Gn_clusterGraph ω R) h

open Classical in


theorem bc70_spanningForest_degree_pos (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ)
    {u v : (↑(box d R) : Type)} (hv : v ≠ u)
    (h : (bc70_Gn_clusterGraph ω R).Reachable u v) :
    1 ≤ (bc70_spanningForest ω R).degree u :=
  osf_spanForest_degree_pos_of_reachable_ne (bc70_Gn_clusterGraph ω R) hv h


theorem bc70_spanningForest_leaf_count {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (univ.filter (fun v => G.degree v = 1)).card :=
  flc2_forest_internal_le_leaves G hacyc hmin


end StatMech.Walls
