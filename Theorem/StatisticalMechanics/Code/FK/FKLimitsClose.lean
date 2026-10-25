/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Def.StatisticalMechanics.Code.FK.FKLimitsClose
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


theorem flc_vrad_le (v : Site d) (i : Fin d) : (v i).natAbs ≤ flc_vrad v :=
  Finset.le_sup (f := fun i => (v i).natAbs) (Finset.mem_univ i)


theorem flc_box_subset_transBox (v : Site d) {a m : ℕ} (hcm : a + flc_vrad v ≤ m) :
    box d a ⊆ fvs_transBox d m v := by
  intro y hy
  change (y - v) ∈ box d m
  intro i
  have hyi : (y i).natAbs ≤ a := hy i
  have hvi : (v i).natAbs ≤ flc_vrad v := flc_vrad_le v i
  have : ((y - v) i) = y i - v i := by simp [Pi.sub_apply]
  rw [this]
  calc (y i - v i).natAbs ≤ (y i).natAbs + (v i).natAbs := Int.natAbs_sub_le _ _
    _ ≤ a + flc_vrad v := Nat.add_le_add hyi hvi
    _ ≤ m := hcm


theorem flc_transBox_subset_box (v : Site d) (m : ℕ) :
    fvs_transBox d m v ⊆ box d (m + flc_vrad v) := by
  intro y hy
  have hy' : (y - v) ∈ box d m := hy
  intro i
  have hyi : ((y - v) i).natAbs ≤ m := hy' i
  have hvi : (v i).natAbs ≤ flc_vrad v := flc_vrad_le v i
  have hsub : ((y - v) i) = y i - v i := by simp [Pi.sub_apply]
  have hyeq : y i = (y i - v i) + v i := by ring
  calc (y i).natAbs = ((y i - v i) + v i).natAbs := by rw [← hyeq]
    _ ≤ (y i - v i).natAbs + (v i).natAbs := Int.natAbs_add_le _ _
    _ = ((y - v) i).natAbs + (v i).natAbs := by rw [hsub]
    _ ≤ m + flc_vrad v := Nat.add_le_add hyi hvi


end FK
end StatMech
