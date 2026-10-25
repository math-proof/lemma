/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc105contraction
import Theorem.StatisticalMechanics.Code.Walls.bc101mengergap
import Theorem.StatisticalMechanics.Code.Walls.bc73sublattice.Part5
import Def.StatisticalMechanics.Code.Walls.bc106separated
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


theorem bc106_origin_onSublattice (L : ℕ) : bc73_onSublattice L (0 : Site d) := by
  intro i; simp


theorem bc106_boxes_disjoint {L : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {y z : Site d}
    (hy : bc106_SeparatedCoarseTrif ω L y) (hz : bc106_SeparatedCoarseTrif ω L z) (hne : y ≠ z) :
    Disjoint (bc61_boxAround d L y) (bc61_boxAround d L z) :=
  bc73_sublattice_boxes_disjoint hy.2 hz.2 hne


theorem bc106_far_of_separated {L : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {y z : Site d}
    (hy : bc106_SeparatedCoarseTrif ω L y) (hz : bc106_SeparatedCoarseTrif ω L z) (hne : y ≠ z) :
    ∃ i, 2 * L < ((y - z) i).natAbs :=
  bc73_far_of_onSublattice hy.2 hz.2 hne


theorem bc106_isCoarseTrif_of_separated {L : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {y : Site d}
    (h : bc106_SeparatedCoarseTrif ω L y) : bc61_IsCoarseTrifurcation ω L y := h.1


theorem bc106_gnTrif_of_separated {L : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {y : Site d}
    (h : bc106_SeparatedCoarseTrif ω L y) : bc67_IsGnTrifurcation ω L y :=
  bc67_gnTrif_of_coarseTrif ω L y h.1


theorem bc106_ιU_injective_free {L : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {y z : Site d}
    (hy : bc106_SeparatedCoarseTrif ω L y) (hz : bc106_SeparatedCoarseTrif ω L z) (hyz : y = z) :
    y = z := hyz


theorem bc106_supervertex_sites_distinct {L : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {y z : Site d}
    (hy : bc106_SeparatedCoarseTrif ω L y) (hz : bc106_SeparatedCoarseTrif ω L z) (hne : y ≠ z) :
    y ∈ bc61_boxAround d L y ∧ y ∉ bc61_boxAround d L z := by
  refine ⟨bc105_centre_mem_own_box L y, ?_⟩
  intro hmem
  exact (Finset.disjoint_left.mp (bc106_boxes_disjoint hy hz hne)
    (bc105_centre_mem_own_box L y)) hmem


theorem bc106_resVec_eq_zero {L : ℕ} {y : Site d} (hy : bc73_onSublattice L y) :
    bc73_resVec L y = 0 := by
  funext i
  have hpos : (0 : ℤ) < 2 * L + 1 := by positivity
  have hdvd : (2 * L + 1 : ℤ) ∣ y i := hy i
  have hmod : y i % (2 * L + 1 : ℤ) = 0 := Int.emod_eq_zero_of_dvd hdvd
  apply Fin.ext
  simp only [bc73_resVec, hmod]
  rfl


end StatMech.Walls
