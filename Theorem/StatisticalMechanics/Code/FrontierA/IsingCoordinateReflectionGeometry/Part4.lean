/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateMerge.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionGeometry.Part4


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation

variable {d : Nat}


theorem subset_isingCoordinateSymmetricHull
    (K : Finset (Site d)) (i : Fin d) (m : Int) :
    K ⊆ isingCoordinateSymmetricHull K i m := by
  intro x hx
  exact Finset.mem_union_left _ hx

theorem mem_isingCoordinateSymmetricHull_reflect_iff
    (K : Finset (Site d)) (i : Fin d) (m : Int) (x : Site d) :
    x ∈ isingCoordinateSymmetricHull K i m ↔
      isingCoordinateReflect i m x ∈
        isingCoordinateSymmetricHull K i m := by
  classical
  unfold isingCoordinateSymmetricHull
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      apply Finset.mem_union_left
      rw [← hyx, isingCoordinateReflect_involutive]
      exact hy
  · intro hx
    have hr := (show isingCoordinateReflect i m
        (isingCoordinateReflect i m x) ∈
          K ∪ K.image (isingCoordinateReflect i m) by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨isingCoordinateReflect i m x, hx, rfl⟩)
      · obtain ⟨y, hy, hyr⟩ := Finset.mem_image.mp hx
        apply Finset.mem_union_left
        rw [← hyr, isingCoordinateReflect_involutive]
        exact hy)
    simpa using hr

end StatMech.FrontierA
