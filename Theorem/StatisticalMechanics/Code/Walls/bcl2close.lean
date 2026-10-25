/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcl2close.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bclclose.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


theorem bcl2_threeMeetBox_subset_top (n : ℕ) :
    threeMeetBox 2 n ⊆ {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} := by
  intro ω hω
  exact hω.1


theorem bcl2_tripleEvent_pos_of_threeMeetBox (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n)) :
    ∃ (m : ℕ) (x y z : Site 2),
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bxp_tripleEvent 2 m x y z) := by
  have htop : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} :=
    lt_of_lt_of_le hpos (measure_mono (bcl2_threeMeetBox_subset_top n))
  exact bxp_exists_triple_pos (d := 2) p hp1 htop


end StatMech.Walls
