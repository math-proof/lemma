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
import Def.StatisticalMechanics.Code.Walls.bxpxpos.Part2
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


theorem bxp_threeMeetBox_subset_iUnion (d n : ℕ) :
    threeMeetBox d n ⊆ ⋃ x, ⋃ y, ⋃ z, bxp_tripleEvent d n x y z := by
  intro ω hω
  obtain ⟨htop, x, y, z, hx, hy, hz, hix, hiy, hiz, h12, h13, h23⟩ := hω
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨z,
    htop, hx, hy, hz, hix, hiy, hiz, h12, h13, h23⟩⟩⟩


theorem bxp_exists_triple_pos (p : ℝ≥0) (hp1 : p ≤ 1)
    (htop : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
      {ω | numInfiniteClusters d ω = ⊤}) :
    ∃ (n : ℕ) (x y z : Site d),
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (bxp_tripleEvent d n x y z) := by
  classical
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 with hμ
  obtain ⟨n, hn⟩ := exists_threeMeetBox_pos μ htop
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hu : μ (⋃ x, ⋃ y, ⋃ z, bxp_tripleEvent d n x y z) = 0 := by
    refine measure_iUnion_null fun x => measure_iUnion_null fun y =>
      measure_iUnion_null fun z => ?_
    exact hcon n x y z
  have h0 : μ (threeMeetBox d n) = 0 :=
    le_antisymm ((measure_mono (bxp_threeMeetBox_subset_iUnion d n)).trans_eq hu) bot_le
  exact absurd h0 (ne_of_gt hn)

end StatMech.Walls
