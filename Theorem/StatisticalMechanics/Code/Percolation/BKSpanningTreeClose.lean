/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKSpanningTreeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoundaryPruningClose.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bst_connected_has_spanningTree {V : Type*} (G : SimpleGraph V) (hG : G.Connected) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree := by
  obtain ⟨T, hle, hT⟩ := hG.exists_isTree_le
  exact ⟨T, hle, hT⟩


theorem bst_treeForestData_one_cluster (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bpr_TreeForestData ω n)
    {x y : Site d} (hxbox : x ∈ box d n) (hxtri : IsTrifurcation d ω x)
    (hybox : y ∈ box d n) (hytri : IsTrifurcation d ω y) :
    Connected d ω x y := by
  classical
  obtain ⟨W, _, _, G, _, π, ιT, br, lamL, hTree, _hWcard, hπ, _hπinj,
    hπιT, _hιinj, _hbr, _hlammap, _hlaminj⟩ := h
  
  set f : G →g (openSubgraph d ω) :=
    { toFun := π, map_rel' := fun {a b} hab => hπ a b hab } with hf
  
  have hreach : G.Reachable (ιT x) (ιT y) := hTree.connected.preconnected (ιT x) (ιT y)
  
  have hmap : (openSubgraph d ω).Reachable (π (ιT x)) (π (ιT y)) := hreach.map f
  rw [hπιT x hxbox hxtri, hπιT y hybox hytri] at hmap
  exact hmap


theorem bst_treeForestData_refutable_of_twoClusters (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x y : Site d} (hxbox : x ∈ box d n) (hxtri : IsTrifurcation d ω x)
    (hybox : y ∈ box d n) (hytri : IsTrifurcation d ω y)
    (hsep : ¬ Connected d ω x y) :
    ¬ bpr_TreeForestData ω n := fun h =>
  hsep (bst_treeForestData_one_cluster ω n h hxbox hxtri hybox hytri)


end Percolation
end StatMech
