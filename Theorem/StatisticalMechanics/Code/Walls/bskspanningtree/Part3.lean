/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bctconnectedtree.Part3
import Def.StatisticalMechanics.Code.Walls.bskspanningtree.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bsk_exploration_of_connectedForestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bsk_ConnectedForestData ω L R) : bfg_GenuineExploration ω L R := by
  obtain ⟨V, Leaf, _, _, _, _, _, H, par, trifIdx, compLeaf, hH, hall3, hinj, hcompB, hcompD⟩ := h
  exact bsk_exploration_of_augmentedTree ω L R H par hH trifIdx compLeaf hall3 hinj hcompB hcompD


theorem bsk_bk_count_of_connectedForest (L R : ℕ)
    (hdata : ∀ ω : ConfigSpace (Sym2 (Site d)), bsk_ConnectedForestData ω L R) :
    ∀ ω : ConfigSpace (Sym2 (Site d)),
      (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R :=
  fun ω => bfg_genuineTcount_le_boundary ω L R (bsk_exploration_of_connectedForestData ω L R (hdata ω))


theorem bsk_status :
    
    (∀ {V Leaf : Type*} (H : SimpleGraph V) (par : Leaf → V), H.IsAcyclic →
      (bsk_augG H par).IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bsk_ConnectedForestData ω L R →
      bfg_GenuineExploration ω L R) ∧
    
    (∀ {V : Type} (G : SimpleGraph V), G.Connected → ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree) ∧
    
    (∀ (L R : ℕ), (∀ ω : ConfigSpace (Sym2 (Site d)), bsk_ConnectedForestData ω L R) →
      ∀ ω : ConfigSpace (Sym2 (Site d)),
        (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R) :=
  ⟨fun H par hH => bsk_augG_acyclic H par hH,
   fun ω L R h => bsk_exploration_of_connectedForestData ω L R h,
   fun G h => bsk_exists_spanningTree G h,
   fun L R hdata ω => bsk_bk_count_of_connectedForest L R hdata ω⟩

end StatMech.Walls
