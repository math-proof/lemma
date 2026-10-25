/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bependpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfxtrifexist
import Theorem.StatisticalMechanics.Code.Walls.bependpoint
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


def bep_encounter (p : ℝ≥0) (hp1 : p ≤ 1) : Prop :=
  0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} →
    ∃ a₁ a₂ a₃ : Site 2,
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        (NeighborTrifPrecursor 2 a₁ a₂ a₃)


end StatMech.Walls
