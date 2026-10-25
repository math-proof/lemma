/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc75spanningtree.Part4
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Def.StatisticalMechanics.Code.Walls.bc80gntrifcount
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


open Classical in


theorem bc80_branch_le_leaf (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) :
    (bc80_branchFinset ω L R c S).card ≤ (bc80_leafFinset ω L R c S).card := by
  classical
  have hacyc : (bc75_spanForest ω L R c S).IsAcyclic := bc75_spanForest_acyclic ω L R c S
  
  have hkey := flc2_forest_internal_le_leaves (bc75_spanForest ω L R c S) hacyc hmin
  simpa only [bc80_branchFinset, bc80_leafFinset] using hkey

open Classical in


theorem bc80_GnTrifCount_le_leaf (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) :
    bc80_GnTrifCount ω L R c S ≤ (bc80_leafFinset ω L R c S).card :=
  bc80_branch_le_leaf ω L R c S hmin


end StatMech.Walls
