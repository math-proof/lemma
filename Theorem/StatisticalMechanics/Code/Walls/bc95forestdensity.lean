/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc95forestdensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc94density.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc95_spanForest_exists {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧ (∀ {u v : V}, G.Reachable u v → F.Reachable u v) :=
  ⟨osf_spanForest G, osf_spanForest_le G, osf_spanForest_acyclic G,
    fun {u v} h => osf_spanForest_reachable_of G h⟩


theorem bc95_spanForest_degree_pos {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel (osf_spanForest G).Adj] {u v : V} (hv : v ≠ u) (h : G.Reachable u v) :
    1 ≤ (osf_spanForest G).degree u :=
  osf_spanForest_degree_pos_of_reachable_ne G hv h


theorem bc95_boxOpenForest_of_harmbox (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n)
    (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
    bst_BoxOpenForest ω n :=
  bc90_boxOpenForest_of_genuine_armsInBox ω n hn hcanon harmbox hexists


end StatMech.Walls
