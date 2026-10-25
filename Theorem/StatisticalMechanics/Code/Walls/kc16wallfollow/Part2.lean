/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc16wallfollow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc9core
import Def.StatisticalMechanics.Code.Walls.kc16wallfollow
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc16_rightDodge_of_verticalDetour (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hdet : kc16_VerticalDetour Vc R) : ecc_RightDodge Vc R := by
  intro z hzout hzoff hzR hnb
  rcases hdet z hzout hzoff hzR hnb with ⟨k, hoff, hright⟩ | ⟨k, hoff, hright⟩
  · exact kc16_climbUp_step Vc z k hoff hright
  · exact kc16_climbDown_step Vc z k hoff hright


theorem kc16_offSupportReaches_of_verticalDetour (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hdet : kc16_VerticalDetour Vc R) : kc5_OffSupportReachesExterior Vc R :=
  kc9_offSupportReaches_of_rightDodge Vc R (kc16_rightDodge_of_verticalDetour Vc R hdet)


theorem kc16_offSupport_of_row_high (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {w : Site 2} (hw : (R : ℤ) < w 1 ∨ w 1 < -(R : ℤ)) :
    w ∉ Vc.support := by
  intro hmem
  have hbox := hsupp ((oc_mem_supportSet Vc w).mpr hmem) 1
  have habs : |w 1| ≤ (R : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hbox
  rw [abs_le] at habs
  omega


theorem kc16_detour_up_of_homeColumnClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (z : Site 2) (hzrow : z 1 ≤ (R : ℤ))
    (hcol : ∀ j : ℕ, j ≤ ((R : ℤ) + 1 - z 1).toNat →
        (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support) :
    ∃ k : ℕ, (∀ j : ℕ, j ≤ k → (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support) ∧
        (![z 0 + 1, z 1 + (k : ℤ)] : Site 2) ∉ Vc.support := by
  refine ⟨((R : ℤ) + 1 - z 1).toNat, hcol, ?_⟩
  apply kc16_offSupport_of_row_high Vc R hsupp
  left
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  have : (((R : ℤ) + 1 - z 1).toNat : ℤ) = (R : ℤ) + 1 - z 1 := by omega
  rw [this]; omega


theorem kc16_detour_down_of_homeColumnClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (z : Site 2) (hzrow : -(R : ℤ) ≤ z 1)
    (hcol : ∀ j : ℕ, j ≤ ((R : ℤ) + 1 + z 1).toNat →
        (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support) :
    ∃ k : ℕ, (∀ j : ℕ, j ≤ k → (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support) ∧
        (![z 0 + 1, z 1 - (k : ℤ)] : Site 2) ∉ Vc.support := by
  refine ⟨((R : ℤ) + 1 + z 1).toNat, hcol, ?_⟩
  apply kc16_offSupport_of_row_high Vc R hsupp
  right
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  have : (((R : ℤ) + 1 + z 1).toNat : ℤ) = (R : ℤ) + 1 + z 1 := by omega
  rw [this]; omega


end Walls
end StatMech
