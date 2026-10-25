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


namespace StatMech.FrontierA

open scoped BigOperators

open Filter Topology

open StatMech StatMech.Lattice StatMech.Ising StatMech.Percolation

noncomputable section

theorem spin_glue_rectangularPrismConfigEquiv
    (eta : ConfigSpace (Site 3)) (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n)
    (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    spin (glue eta (rectangularPrismConfigEquivSctBoxDobrushin n sigma))
        (rectangularPrismSiteEquivSctBoxDobrushin n v).1 =
      spin sigma v := by
  unfold spin
  rw [glue_mem _ _
    (rectangularPrismSiteEquivSctBoxDobrushin n v).2]
  exact congrArg (fun b : Bool => if b then (1 : Real) else -1)
    (rectangularPrismConfigEquivSctBoxDobrushin_apply n sigma v)

theorem oddPrism_xZero_exterior_not_mem
    (n : Nat) (y z : Fin (2 * n + 1)) :
    coordShift
      (rectangularPrismSiteEquivSctBoxDobrushin n ⟨0, y, z⟩).1
      0 (-1) ∉ box 3 n := by
  intro h
  have h0 := h 0
  simp [coordShift] at h0
  omega

theorem oddPrism_xLast_exterior_not_mem
    (n : Nat) (y z : Fin (2 * n + 1)) :
    coordShift
      (rectangularPrismSiteEquivSctBoxDobrushin n
        ⟨Fin.last (2 * n), y, z⟩).1 0 1 ∉ box 3 n := by
  intro h
  have h0 := h 0
  simp [coordShift, Fin.last] at h0
  omega

theorem oddPrism_yZero_exterior_not_mem
    (n : Nat) (x z : Fin (2 * n + 1)) :
    coordShift
      (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, 0, z⟩).1
      1 (-1) ∉ box 3 n := by
  intro h
  have h1 := h 1
  simp [coordShift] at h1
  omega

theorem oddPrism_yLast_exterior_not_mem
    (n : Nat) (x z : Fin (2 * n + 1)) :
    coordShift
      (rectangularPrismSiteEquivSctBoxDobrushin n
        ⟨x, Fin.last (2 * n), z⟩).1 1 1 ∉ box 3 n := by
  intro h
  have h1 := h 1
  simp [coordShift, Fin.last] at h1
  omega

theorem oddPrism_zZero_exterior_not_mem
    (n : Nat) (x y : Fin (2 * n + 1)) :
    coordShift
      (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, 0⟩).1
      2 1 ∉ box 3 n := by
  intro h
  have h2 := h 2
  simp [coordShift] at h2
  omega

theorem oddPrism_zLast_exterior_not_mem
    (n : Nat) (x y : Fin (2 * n + 1)) :
    coordShift
      (rectangularPrismSiteEquivSctBoxDobrushin n
        ⟨x, y, Fin.last (2 * n)⟩).1 2 (-1) ∉ box 3 n := by
  intro h
  have h2 := h 2
  simp [coordShift, Fin.last] at h2
  omega

theorem spin_glue_plus_of_not_mem
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    {x : Site 3} (hx : x ∉ box 3 n) :
    spin (glue (plusField 3) tau) x = 1 := by
  unfold spin
  rw [glue_not_mem _ _ hx]
  rfl

@[simp] theorem spin_glue_plus_xZero
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (y z : Fin (2 * n + 1)) :
    spin (glue (plusField 3) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n ⟨0, y, z⟩).1
        0 (-1)) = 1 :=
  spin_glue_plus_of_not_mem n tau (oddPrism_xZero_exterior_not_mem n y z)

@[simp] theorem spin_glue_plus_xLast
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (y z : Fin (2 * n + 1)) :
    spin (glue (plusField 3) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n
          ⟨Fin.last (2 * n), y, z⟩).1 0 1) = 1 :=
  spin_glue_plus_of_not_mem n tau (oddPrism_xLast_exterior_not_mem n y z)

@[simp] theorem spin_glue_plus_yZero
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x z : Fin (2 * n + 1)) :
    spin (glue (plusField 3) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, 0, z⟩).1
        1 (-1)) = 1 :=
  spin_glue_plus_of_not_mem n tau (oddPrism_yZero_exterior_not_mem n x z)

@[simp] theorem spin_glue_plus_yLast
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x z : Fin (2 * n + 1)) :
    spin (glue (plusField 3) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n
          ⟨x, Fin.last (2 * n), z⟩).1 1 1) = 1 :=
  spin_glue_plus_of_not_mem n tau (oddPrism_yLast_exterior_not_mem n x z)

@[simp] theorem spin_glue_plus_zZero
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x y : Fin (2 * n + 1)) :
    spin (glue (plusField 3) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, 0⟩).1
        2 1) = 1 :=
  spin_glue_plus_of_not_mem n tau (oddPrism_zZero_exterior_not_mem n x y)

@[simp] theorem spin_glue_plus_zLast
    (n : Nat) (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
    (x y : Fin (2 * n + 1)) :
    spin (glue (plusField 3) tau)
      (coordShift
        (rectangularPrismSiteEquivSctBoxDobrushin n
          ⟨x, y, Fin.last (2 * n)⟩).1 2 (-1)) = 1 :=
  spin_glue_plus_of_not_mem n tau (oddPrism_zLast_exterior_not_mem n x y)


end
end StatMech.FrontierA
