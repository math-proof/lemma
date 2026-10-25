/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc112sepcontract.Part7
import Theorem.StatisticalMechanics.Code.Walls.bc118pathmember
import Theorem.StatisticalMechanics.Code.Walls.bc121trifcount
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


def bc121_Protected (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} (ιU : Site d → (↑S : Type)) (v : (↑S : Type)) : Prop :=
  (v : Site d) ∈ vertexBoundary d R ∨
    (∃ y, y ∈ box d R ∧ bc67_IsGnTrifurcation ω L y ∧ ιU y = v)

end StatMech.Walls
