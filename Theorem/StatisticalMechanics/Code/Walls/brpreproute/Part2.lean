/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brpreproute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bcrboxrep.Part2
import Theorem.StatisticalMechanics.Code.Walls.brtrouteclose
import Def.StatisticalMechanics.Code.Walls.brpreproute
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


@[simp] theorem brp_witArm_zero (R : ℕ) : brp_witArm R 0 = bc57_pt (R : ℤ) 0 := rfl

@[simp] theorem brp_witArm_one (R : ℕ) : brp_witArm R 1 = bc57_pt 0 (R : ℤ) := rfl

@[simp] theorem brp_witArm_two (R : ℕ) : brp_witArm R 2 = bc57_pt 0 (-(R : ℤ)) := rfl


theorem brp_cross_repRoute (L R : ℕ) (hR : L < R) :
    bcr_RepRoute bcr_cross L (bc57_pt 0 0) (brp_witArm R) := by
  have hRz : (L : ℤ) < (R : ℤ) := by exact_mod_cast hR
  unfold bcr_RepRoute
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [brp_witArm_zero, brp_witArm_one, brp_witArm_two] at hij ⊢
  
  · exact absurd rfl hij
  
  · have h := brp_cross_hreach_avoid L (bc57_pt 0 (R : ℤ)) 0 R (fun m => by
      refine brp_off_box_coord 1 ?_
      simp only [Pi.sub_apply, bc57_pt_snd]
      rw [show (0 : ℤ) - (R : ℤ) = -(R : ℤ) by ring, Int.natAbs_neg, Int.natAbs_natCast]
      exact hR)
    rw [zero_add] at h
    exact h
  
  · have h := brp_cross_hreach_avoid L (bc57_pt 0 (-(R : ℤ))) 0 R (fun m => by
      refine brp_off_box_coord 1 ?_
      simp only [Pi.sub_apply, bc57_pt_snd]
      rw [show (0 : ℤ) - -(R : ℤ) = (R : ℤ) by ring, Int.natAbs_natCast]
      exact hR)
    rw [zero_add] at h
    exact h
  
  · have h := brp_cross_vreach_up_avoid L (bc57_pt (R : ℤ) 0) 0 R (fun m => by
      refine brp_off_box_coord 0 ?_
      simp only [Pi.sub_apply, bc57_pt_fst]
      rw [show (0 : ℤ) - (R : ℤ) = -(R : ℤ) by ring, Int.natAbs_neg, Int.natAbs_natCast]
      exact hR)
    rw [zero_add] at h
    exact h
  
  · exact absurd rfl hij
  
  · have h := brp_cross_vreach_up_avoid L (bc57_pt 0 (-(R : ℤ))) 0 R (fun m => by
      refine brp_off_box_coord 1 ?_
      simp only [Pi.sub_apply, bc57_pt_snd]
      rw [show (0 : ℤ) + (m : ℤ) - -(R : ℤ) = (m : ℤ) + (R : ℤ) by ring]
      have : ((m : ℤ) + (R : ℤ)).natAbs = m + R := by
        rw [Int.natAbs_eq_iff]; left; push_cast; ring
      rw [this]; omega)
    rw [zero_add] at h
    exact h
  
  · have h := brp_cross_vreach_down_avoid L (bc57_pt (R : ℤ) 0) 0 R (fun m => by
      refine brp_off_box_coord 0 ?_
      simp only [Pi.sub_apply, bc57_pt_fst]
      rw [show (0 : ℤ) - (R : ℤ) = -(R : ℤ) by ring, Int.natAbs_neg, Int.natAbs_natCast]
      exact hR)
    rw [zero_sub] at h
    exact h
  
  · have h := brp_cross_vreach_down_avoid L (bc57_pt 0 (R : ℤ)) 0 R (fun m => by
      refine brp_off_box_coord 1 ?_
      simp only [Pi.sub_apply, bc57_pt_snd]
      rw [show (0 : ℤ) - (m : ℤ) - (R : ℤ) = -((m : ℤ) + (R : ℤ)) by ring, Int.natAbs_neg]
      have : ((m : ℤ) + (R : ℤ)).natAbs = m + R := by
        rw [Int.natAbs_eq_iff]; left; push_cast; ring
      rw [this]; omega)
    rw [zero_sub] at h
    exact h
  
  · exact absurd rfl hij


theorem brp_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (x : Site d) (a : Fin 3 → Site d),
      x ∈ box d R → bc67_IsGnTrifurcation ω L x →
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x) →
      (∀ i, a i ∈ vertexBoundary d R) → (∀ i, a i ≠ x) → Function.Injective a →
      (∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (a i) (a j)) →
      bcr_RepRoute ω L x a → bgc_TrifForestData ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x : Site d) (tip b : Fin 3 → Site d),
      (∀ i j, i ≠ j → (bc67_contractedLattice ω L (tip j)).Reachable x (b i)) →
      (∀ i j, i ≠ j → (bc67_contractedLattice ω L (tip j)).Reachable (b i) (tip i)) →
      bcr_RepRoute ω L x tip) ∧
    
    (∀ (L R : ℕ), L < R → bcr_RepRoute bcr_cross L (bc57_pt 0 0) (brp_witArm R)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L R x a hxbox hxtri hsingle habdry hxne hainj hsep hroute
    exact brp_trifForestData_of_repRoute ω L R a hxbox hxtri hsingle habdry hxne hainj hsep hroute
  · intro ω L x tip b hentry htail; exact brp_repRoute_of_entry ω L x tip b hentry htail
  · intro L R hR; exact brp_cross_repRoute L R hR

end StatMech.Walls
