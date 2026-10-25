/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgctrifgraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bgfacyclicstep
import Theorem.StatisticalMechanics.Code.Walls.bc70globalforest.Part4
import Theorem.StatisticalMechanics.Code.Walls.bkwburtonkeane
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


theorem bgc_adj_of_openAdj_avoiding (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (t a b : Site d)
    (hab : (openSubgraph d ω).Adj a b)
    (hta : a ∉ bc61_boxAround d L t) (htb : b ∉ bc61_boxAround d L t) :
    (bc67_contractedLattice ω L t).Adj a b := by
  rw [bc67_contractedLattice_adj, openSubgraph_adj] at *
  refine ⟨hab.1, ?_⟩
  
  show removeSites (bc61_boxAround d L t) ω s(a, b) = true
  unfold removeSites
  rw [if_neg, hab.2]
  rintro ⟨t', ht'T, ht'e⟩
  rw [Sym2.mem_iff] at ht'e
  rcases ht'e with rfl | rfl
  · exact hta ht'T
  · exact htb ht'T


theorem bgc_reach_of_openAdj_avoiding (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (t a b : Site d)
    (hab : (openSubgraph d ω).Adj a b)
    (hta : a ∉ bc61_boxAround d L t) (htb : b ∉ bc61_boxAround d L t) :
    (bc67_contractedLattice ω L t).Reachable a b :=
  (bgc_adj_of_openAdj_avoiding ω L t a b hab hta htb).reachable


end StatMech.Walls
