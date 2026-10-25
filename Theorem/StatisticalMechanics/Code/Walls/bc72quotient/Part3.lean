/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc72quotient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc71spanningtree.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Def.StatisticalMechanics.Code.Walls.bc72quotient.Part3
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


theorem bc72_forestNeighbours_of_multiBox (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc72_MultiBoxForestOnQuot ω L R) : bc71_GnForestNeighbours ω L R := h


theorem bc72_count_of_multiBox (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc72_MultiBoxForestOnQuot ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc71_count_of_forestNeighbours ω L R h


theorem bc72_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a : Site d),
      bc67_GnIncident ω L y a → a ∉ bc61_boxAround d L y →
      (bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).Adj y a) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d), bc67_IsGnTrifurcation ω L y →
      ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : y ∈ S)
        (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).Adj),
        3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).degree ⟨y, hyS⟩) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc72_MultiBoxForestOnQuot ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L y a hinc hne; exact bc72_arm_adjacent_to_superVertex hinc hne
  · intro ω L y htri; exact bc72_quot_deg3_of_gnTrif htri
  · intro ω L R h; exact bc72_count_of_multiBox ω L R h

end StatMech.Walls
