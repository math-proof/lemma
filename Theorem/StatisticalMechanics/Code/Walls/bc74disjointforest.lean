/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc73sublattice.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc69count.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
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


theorem bc74_fiber_subset (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) :
    bc73_fiber ω L R c ⊆ bc61_coarseTrifFinset ω L R := by
  classical
  rw [bc73_fiber]
  exact Finset.filter_subset _ _


theorem bc74_fiber_card_le_coarseTcount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) :
    (bc73_fiber ω L R c).card ≤ bc61_coarseTcount ω L R := by
  rw [bc61_coarseTcount]
  exact Finset.card_le_card (bc74_fiber_subset ω L R c)


theorem bc74_sublatticeForest_of_fullCount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) :
    bc73_SublatticeForest ω L R := by
  intro c
  exact le_trans (bc74_fiber_card_le_coarseTcount ω L R c) h


theorem bc74_sublatticeForest_of_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) :
    bc73_SublatticeForest ω L R :=
  bc74_sublatticeForest_of_fullCount ω L R (bc69_coarseTcount_le_boundary ω L R h)


theorem bc74_sublatticeForest_of_forestNeighbours (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc71_GnForestNeighbours ω L R) :
    bc73_SublatticeForest ω L R :=
  bc74_sublatticeForest_of_fullCount ω L R (bc71_count_of_forestNeighbours ω L R h)


theorem bc74_fiber_mem_gnTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) {y : Site d} (hy : y ∈ bc73_fiber ω L R c) :
    bc67_IsGnTrifurcation ω L y := by
  have hmem : y ∈ bc61_coarseTrifFinset ω L R := bc74_fiber_subset ω L R c hy
  rw [bc61_mem_coarseTrifFinset] at hmem
  exact (bc67_coarseTrif_is_G_n_trifurcation ω L y).mp hmem.2


theorem bc74_fiber_disjointBoxes_deg3 (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) {y : Site d} (hy : y ∈ bc73_fiber ω L R c) :
    ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : y ∈ S)
      (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).Adj),
      3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).degree ⟨y, hyS⟩ :=
  bc73_disjointBoxes_deg3 (bc74_fiber_mem_gnTrif ω L R c hy)


theorem bc74_fiber_leaf_inject {p : Site d → Prop} (S : Set (Subtype p)) :
    Set.InjOn (Subtype.val : Subtype p → Site d) S :=
  bc69_subtypeVal_injOn S


end StatMech.Walls
