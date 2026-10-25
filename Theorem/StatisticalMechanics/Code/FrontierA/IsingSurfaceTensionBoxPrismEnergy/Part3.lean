/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteVolume.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoundaryBridge.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part2


namespace StatMech.FrontierA

open scoped BigOperators

open Filter Topology

open StatMech StatMech.Lattice StatMech.Ising StatMech.Percolation

noncomputable section

theorem oddRectangularPrismMeanNegEnergy_eq_fvMeanNegEnergy
    (J beta : Real) (n : Nat) :
    oddRectangularPrismMeanNegEnergy J beta n =
      J * fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n)
        (beta * J) 0 := by
  unfold oddRectangularPrismMeanNegEnergy fvMeanNegEnergy
  rw [rectangularPrismPlusPartition_eq_fvZ]
  rw [← Equiv.sum_comp (rectangularPrismConfigEquivSctBoxDobrushin n)]
  rw [← mul_div_assoc]
  apply congrArg (fun x => x / fvZ (plusField 3) n
    (bondFinsetTouch 3 n) (beta * J) 0)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [rectangularPrismPlusEnergy_eq_mul_fvEnergy]
  unfold fvWeight
  ring_nf


theorem hasDerivAt_log_rectangularPrismPlusPartition
    (J beta : Real) (n : Nat) :
    HasDerivAt
      (fun b => Real.log
        (rectangularPrismPlusPartition J b (2 * n + 1) (2 * n + 1) n))
      (oddRectangularPrismMeanNegEnergy J beta n) beta := by
  have hfun :
      (fun b => Real.log
        (rectangularPrismPlusPartition J b (2 * n + 1) (2 * n + 1) n)) =
      (fun b => Real.log
        (fvZ (plusField 3) n (bondFinsetTouch 3 n) (b * J) 0)) := by
    funext b
    rw [rectangularPrismPlusPartition_eq_fvZ]
  rw [hfun, oddRectangularPrismMeanNegEnergy_eq_fvMeanNegEnergy]
  convert
    (hasDerivAt_log_fvZ_beta (plusField 3) n (bondFinsetTouch 3 n)
      (beta * J) 0).comp beta ((hasDerivAt_id beta).mul_const J) using 1 <;>
    ring


theorem spin_glue_interface_of_not_mem_coord
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    {x : Site 3} (hx : x ∉ box 3 n) (z : Fin (2 * n + 1))
    (hx2 : x 2 = (n : Int) - z.val) :
    spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau) x =
      oddRectangularPrismDobrushinSign n z := by
  unfold spin oddRectangularPrismDobrushinSign
  rw [glue_not_mem _ _ hx, interfaceField_apply]
  have hx2' : x (⟨2, by omega⟩ : Fin 3) = (n : Int) - z.val := by
    convert hx2
  rw [hx2']
  by_cases hz : n < z.val
  · have hneg : ¬ (0 : Int) ≤ (n : Int) - z.val := by
      rw [not_le]
      exact sub_neg.mpr (by exact_mod_cast hz)
    simp [hz, hneg]
  · have hnonneg : (0 : Int) ≤ (n : Int) - z.val := by
      exact sub_nonneg.mpr (by
        exact_mod_cast (Nat.le_of_not_gt hz))
    simp [hz, hnonneg]


theorem spin_glue_interface_of_not_mem_coord_at
    (n : Nat) (i : Fin 3) (hi : i.val = 2)
    (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    {x : Site 3} (hx : x ∉ box 3 n) (z : Fin (2 * n + 1))
    (hx2 : x 2 = (n : Int) - z.val) :
    spin (glue (interfaceField i) tau) x =
      oddRectangularPrismDobrushinSign n z := by
  have hi' : i = (⟨2, by omega⟩ : Fin 3) := Fin.ext hi
  rw [hi']
  exact spin_glue_interface_of_not_mem_coord n tau hx z hx2

@[simp] theorem spin_glue_interface_xZero
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (y z : Fin (2 * n + 1)) :
    spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n ⟨0, y, z⟩).1
        0 (-1)) = oddRectangularPrismDobrushinSign n z := by
  apply spin_glue_interface_of_not_mem_coord n tau
    (oddPrism_xZero_exterior_not_mem n y z) z
  simp [coordShift]

@[simp] theorem spin_glue_interface_xLast
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (y z : Fin (2 * n + 1)) :
    spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n
          ⟨Fin.last (2 * n), y, z⟩).1 0 1) =
      oddRectangularPrismDobrushinSign n z := by
  apply spin_glue_interface_of_not_mem_coord n tau
    (oddPrism_xLast_exterior_not_mem n y z) z
  simp [coordShift]

@[simp] theorem spin_glue_interface_yZero
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x z : Fin (2 * n + 1)) :
    spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, 0, z⟩).1
        1 (-1)) = oddRectangularPrismDobrushinSign n z := by
  apply spin_glue_interface_of_not_mem_coord n tau
    (oddPrism_yZero_exterior_not_mem n x z) z
  simp [coordShift]

@[simp] theorem spin_glue_interface_yLast
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x z : Fin (2 * n + 1)) :
    spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n
          ⟨x, Fin.last (2 * n), z⟩).1 1 1) =
      oddRectangularPrismDobrushinSign n z := by
  apply spin_glue_interface_of_not_mem_coord n tau
    (oddPrism_yLast_exterior_not_mem n x z) z
  simp [coordShift]

@[simp] theorem spin_glue_interface_zZero
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x y : Fin (2 * n + 1)) :
    spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, 0⟩).1
        2 1) = oddRectangularPrismDobrushinSign n 0 := by
  unfold spin oddRectangularPrismDobrushinSign
  rw [glue_not_mem _ _ (oddPrism_zZero_exterior_not_mem n x y),
    interfaceField_apply]
  simp [coordShift]
  omega

@[simp] theorem spin_glue_interface_zLast
    (n : Nat) (hn : 0 < n)
    (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x y : Fin (2 * n + 1)) :
    spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n
          ⟨x, y, Fin.last (2 * n)⟩).1 2 (-1)) =
      oddRectangularPrismDobrushinSign n (Fin.last (2 * n)) := by
  unfold spin oddRectangularPrismDobrushinSign
  rw [glue_not_mem _ _ (oddPrism_zLast_exterior_not_mem n x y),
    interfaceField_apply]
  simp [coordShift, Fin.last, hn]
  omega

theorem spin_glue_interface_zZero_at
    (n : Nat) (i : Fin 3) (hi : i.val = 2)
    (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x y : Fin (2 * n + 1)) :
    spin (glue (interfaceField i) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, 0⟩).1
        2 1) = oddRectangularPrismDobrushinSign n 0 := by
  have hi' : i = (⟨2, by omega⟩ : Fin 3) := Fin.ext hi
  rw [hi']
  exact spin_glue_interface_zZero n tau x y

theorem spin_glue_interface_zLast_at
    (n : Nat) (hn : 0 < n) (i : Fin 3) (hi : i.val = 2)
    (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x y : Fin (2 * n + 1)) :
    spin (glue (interfaceField i) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n
          ⟨x, y, Fin.last (2 * n)⟩).1 2 (-1)) =
      oddRectangularPrismDobrushinSign n (Fin.last (2 * n)) := by
  have hi' : i = (⟨2, by omega⟩ : Fin 3) := Fin.ext hi
  rw [hi']
  exact spin_glue_interface_zLast n hn tau x y


end
end StatMech.FrontierA
