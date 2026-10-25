/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bptpartitioncount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bsdsepdegree
import Theorem.StatisticalMechanics.Code.Walls.bc69count.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkgclassicalforest.Part2
import Theorem.StatisticalMechanics.Code.Walls.bptpartitioncount
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


def bpt_ClassesLaminar (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∀ (x x' a b : Site d), bc67_IsGnTrifurcation ω L x → bc67_IsGnTrifurcation ω L x' →
    a ∈ vertexBoundary d R → b ∈ vertexBoundary d R →
    bpt_boundaryClass ω L R x a ⊆ bpt_boundaryClass ω L R x' b ∨
    bpt_boundaryClass ω L R x' b ⊆ bpt_boundaryClass ω L R x a ∨
    Disjoint (bpt_boundaryClass ω L R x a) (bpt_boundaryClass ω L R x' b)


end StatMech.Walls
