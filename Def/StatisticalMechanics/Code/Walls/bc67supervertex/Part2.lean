/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc66assembly
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Theorem.StatisticalMechanics.Code.Walls.bc67supervertex
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc67_IsGnTrifurcation (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    
    (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
    
    ((cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧
     (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧
     (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) ∧
    
    (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
     ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
     ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃)


end StatMech.Walls
