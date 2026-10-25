/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

theorem oddPrismSurfaceLow_card_le (n r : Nat) :
    (oddPrismSurfaceLow n r).card <= r := by
  let s := oddPrismSurfaceLow n r
  have hinj : Function.Injective (fun i : Fin (2 * n + 1) => i.val) :=
    fun i j h => Fin.ext h
  have himage : Finset.image (fun i : Fin (2 * n + 1) => i.val) s <=
      Finset.range r := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  calc
    s.card = (Finset.image (fun i : Fin (2 * n + 1) => i.val) s).card :=
      (Finset.card_image_of_injective s hinj).symm
    _ <= (Finset.range r).card := Finset.card_le_card himage
    _ = r := Finset.card_range r

theorem oddPrismSurfaceHigh_card_le (n r : Nat) :
    (oddPrismSurfaceHigh n r).card <= r := by
  let s := oddPrismSurfaceHigh n r
  let f : Fin (2 * n + 1) -> Nat := fun i => 2 * n - i.val
  have hinj : Function.Injective f := by
    intro i j h
    apply Fin.ext
    dsimp [f] at h
    have hi : i.val <= 2 * n := by omega
    have hj : j.val <= 2 * n := by omega
    omega
  have himage : Finset.image f s <= Finset.range r := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_range.mpr
    have hi' := (Finset.mem_filter.mp hi).2
    have hiv : i.val <= 2 * n := by omega
    dsimp [f]
    omega
  calc
    s.card = (Finset.image f s).card :=
      (Finset.card_image_of_injective s hinj).symm
    _ <= (Finset.range r).card := Finset.card_le_card himage
    _ = r := Finset.card_range r

theorem oddPrismSurface_not_interior_subset_boundary
    (n r : Nat) :
    oddPrismSurfaceNonInterior n r <=
      oddPrismSurfaceBoundaryPairs n r := by
  classical
  intro q hq
  unfold oddPrismSurfaceNonInterior at hq
  have hnot := (Finset.mem_filter.mp hq).2
  simp only [oddPrismSurfaceInterior] at hnot
  simp only [oddPrismSurfaceBoundaryPairs, Finset.mem_union,
    Finset.mem_product, Finset.mem_univ, and_true,
    oddPrismSurfaceLow, oddPrismSurfaceHigh, Finset.mem_filter,
    true_and]
  omega

theorem oddPrismSurfaceBoundaryPairs_card_le (n r : Nat) :
    (oddPrismSurfaceBoundaryPairs n r).card <=
      4 * r * (2 * n + 1) := by
  let U : Finset (Fin (2 * n + 1)) := Finset.univ
  have hU : U.card = 2 * n + 1 := by simp [U]
  have hlow := oddPrismSurfaceLow_card_le n r
  have hhigh := oddPrismSurfaceHigh_card_le n r
  have h1 : (oddPrismSurfaceLow n r ×ˢ U).card <= r * (2 * n + 1) := by
    rw [Finset.card_product, hU]
    exact Nat.mul_le_mul_right _ hlow
  have h2 : (oddPrismSurfaceHigh n r ×ˢ U).card <= r * (2 * n + 1) := by
    rw [Finset.card_product, hU]
    exact Nat.mul_le_mul_right _ hhigh
  have h3 : (U ×ˢ oddPrismSurfaceLow n r).card <= r * (2 * n + 1) := by
    rw [Finset.card_product, hU]
    nlinarith
  have h4 : (U ×ˢ oddPrismSurfaceHigh n r).card <= r * (2 * n + 1) := by
    rw [Finset.card_product, hU]
    nlinarith
  have h12 : (oddPrismSurfaceLow n r ×ˢ U ∪
      oddPrismSurfaceHigh n r ×ˢ U).card <=
      (oddPrismSurfaceLow n r ×ˢ U).card +
        (oddPrismSurfaceHigh n r ×ˢ U).card :=
    Finset.card_union_le _ _
  dsimp only [oddPrismSurfaceBoundaryPairs]
  calc
    ((oddPrismSurfaceLow n r ×ˢ U ∪
        oddPrismSurfaceHigh n r ×ˢ U ∪
        U ×ˢ oddPrismSurfaceLow n r) ∪
        U ×ˢ oddPrismSurfaceHigh n r).card <=
      (oddPrismSurfaceLow n r ×ˢ U ∪
        oddPrismSurfaceHigh n r ×ˢ U ∪
        U ×ˢ oddPrismSurfaceLow n r).card +
          (U ×ˢ oddPrismSurfaceHigh n r).card := Finset.card_union_le _ _
    _ <= ((oddPrismSurfaceLow n r ×ˢ U ∪
        oddPrismSurfaceHigh n r ×ˢ U).card +
          (U ×ˢ oddPrismSurfaceLow n r).card) +
          (U ×ˢ oddPrismSurfaceHigh n r).card := by
      gcongr
      exact Finset.card_union_le _ _
    _ <= 4 * r * (2 * n + 1) := by
      rw [show 4 * r * (2 * n + 1) =
        r * (2 * n + 1) + r * (2 * n + 1) +
          r * (2 * n + 1) + r * (2 * n + 1) by ring]
      omega


end
end StatMech.FrontierA
