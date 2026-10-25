/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc94density.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc93badbox
import Theorem.StatisticalMechanics.Code.Walls.bc90boxopenforest
import Theorem.StatisticalMechanics.Code.Walls.bc89genuinetrifae
import Def.StatisticalMechanics.Code.Walls.bc94density
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


theorem bc94_genuineTcount_le_boundary_of_forest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bst_BoxOpenForest ω n) :
    bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n :=
  bc89_genuineTcount_le_boundary_of_openForest ω n h


theorem bc94_genuineTcount_le_boundary_of_inputs (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
    bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n :=
  bc90_genuineTcount_le_boundary_of_genuine_armsInBox ω n hn hcanon harmbox


theorem bc94_count_bound_under_top (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (_hN : numInfiniteClusters d ω = ⊤) (h : bst_BoxOpenForest ω n) :
    bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n :=
  bc94_genuineTcount_le_boundary_of_forest ω n h


theorem bc94_count_bound_under_ge_two (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (_hN : 2 ≤ numInfiniteClusters d ω)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
    bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n :=
  bc94_genuineTcount_le_boundary_of_inputs ω n hn hcanon harmbox


end StatMech.Walls
