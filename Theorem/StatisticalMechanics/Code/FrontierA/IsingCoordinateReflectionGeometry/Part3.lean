/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateMerge.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionGeometry.Part3


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation

variable {d : Nat}


theorem isingCoordinateReflect_fixed
    (i : Fin d) (m : Int) (x : Site d)
    (hx : isingCoordinatePlane i m x) :
    isingCoordinateReflect i m x = x := by
  funext a
  by_cases hai : a = i
  · subst a
    simp [isingCoordinatePlane] at hx ⊢
    omega
  · exact isingCoordinateReflect_apply_of_ne i a hai m x

theorem isingCoordinateReflect_centered
    (i : Fin d) (m : Int) (x : Site d) :
    2 * isingCoordinateReflect i m x i - m = -(2 * x i - m) := by
  simp
  ring

theorem isingCoordinateReflect_lower_of_upper
    (i : Fin d) (m : Int) (x : Site d)
    (hp : ¬ isingCoordinatePlane i m x)
    (hl : ¬ isingCoordinateLower i m x) :
    isingCoordinateLower i m (isingCoordinateReflect i m x) := by
  unfold isingCoordinatePlane at hp
  unfold isingCoordinateLower at hl ⊢
  simp only [isingCoordinateReflect_apply_same]
  omega

theorem isingCoordinateReflect_not_plane
    (i : Fin d) (m : Int) (x : Site d)
    (hp : ¬ isingCoordinatePlane i m x) :
    ¬ isingCoordinatePlane i m (isingCoordinateReflect i m x) := by
  intro hr
  apply hp
  unfold isingCoordinatePlane at hr ⊢
  simp only [isingCoordinateReflect_apply_same] at hr
  omega

theorem isingCoordinateReflect_not_lower_of_lower
    (i : Fin d) (m : Int) (x : Site d)
    (hl : isingCoordinateLower i m x) :
    ¬ isingCoordinateLower i m (isingCoordinateReflect i m x) := by
  unfold isingCoordinateLower at hl ⊢
  simp only [isingCoordinateReflect_apply_same]
  omega


theorem coordinateReflect_eq_of_adj_crossing
    (i : Fin d) (m : Int) {x y : Site d}
    (hxy : (hypercubicLattice d).Adj x y)
    (hxl : isingCoordinateLower i m x)
    (hyp : ¬ isingCoordinatePlane i m y)
    (hyl : ¬ isingCoordinateLower i m y) :
    isingCoordinateReflect i m x = y := by
  obtain ⟨a, b, rfl⟩ := adj_exists_dir hxy
  by_cases hai : a = i
  · subst a
    cases b with
    | false =>
        exfalso
        apply hyl
        unfold isingCoordinateLower at hxl ⊢
        simp [coordShift, stepSign]
        omega
    | true =>
        have hm : m = 2 * x i + 1 := by
          unfold isingCoordinateLower at hxl hyl
          unfold isingCoordinatePlane at hyp
          simp [coordShift, stepSign] at hyp hyl
          omega
        funext q
        by_cases hqi : q = i
        · subst q
          simp [coordShift, stepSign, hm]
          omega
        · rw [isingCoordinateReflect_apply_of_ne i q hqi]
          simp [coordShift, Function.update_of_ne hqi]
  · have hiUpdate : coordShift x a (stepSign b) i = x i := by
      simp [coordShift, Function.update_of_ne (Ne.symm hai)]
    rw [isingCoordinateLower, hiUpdate] at hyl
    exact absurd hxl hyl

theorem coordinateReflect_eq_of_adj_crossing_symm
    (i : Fin d) (m : Int) {x y : Site d}
    (hxy : (hypercubicLattice d).Adj x y)
    (hyl : isingCoordinateLower i m y)
    (hxp : ¬ isingCoordinatePlane i m x)
    (hxl : ¬ isingCoordinateLower i m x) :
    isingCoordinateReflect i m y = x :=
  coordinateReflect_eq_of_adj_crossing i m hxy.symm hyl hxp hxl


end StatMech.FrontierA
