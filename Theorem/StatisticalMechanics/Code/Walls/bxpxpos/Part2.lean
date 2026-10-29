/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bxpxpos.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bmfmergefree.Part2
import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
import Theorem.StatisticalMechanics.Code.Percolation.PrivateArmProve.Part2
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Def.StatisticalMechanics.Code.Walls.bxpxpos
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


variable {d : ℕ}


theorem bxp_Y_subset_X : bxp_Y ⊆ bmf_X := by
  rintro ω ⟨⟨h01, h02, h03⟩, ⟨hi1, hi2, hi3⟩, ⟨hd12, hd13, hd23⟩⟩
  exact ⟨⟨bxp_infinite_removeSite ω h01 hi1, bxp_infinite_removeSite ω h02 hi2,
      bxp_infinite_removeSite ω h03 hi3⟩,
    bxp_notConnected_removeSite ω hd12, bxp_notConnected_removeSite ω hd13,
    bxp_notConnected_removeSite ω hd23⟩


theorem bxp_hXpos_of_fullPos (p : NNReal) (hp1 : p ≤ 1)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 bxp_Y) :
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 bmf_X :=
  lt_of_lt_of_le hpos (measure_mono bxp_Y_subset_X)


end StatMech.Walls
