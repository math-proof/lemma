/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfglobalforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc122carrier.Part5
import Theorem.StatisticalMechanics.Code.Walls.bgfglobalforest
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


def bgf_WithinHubTips (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (arm : Site d → Fin 3 → Site d) :
    Prop :=
  ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
    (∀ j, arm y j ∈ vertexBoundary d R) ∧
    (∀ j k, j ≠ k → ¬ (bc67_contractedLattice ω L y).Reachable (arm y j) (arm y k))


end StatMech.Walls
