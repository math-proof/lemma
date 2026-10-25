/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem isingRadialGridCoordinate_cellPoint
    (mesh : Real) (hmesh : mesh ≠ 0) (i j : Nat) (x y : Real) :
    isingRadialGridCoordinate mesh
        (isingRadialGridCellPoint mesh i j x y) =
      ((i : Real) + x, (j : Real) + y) := by
  apply Prod.ext <;>
    simp [isingRadialGridCoordinate, isingRadialGridCellPoint, hmesh] <;>
    field_simp <;> ring

theorem isingRadialGridCellPoint_sub
    (mesh : Real) (i j : Nat) (x x' y y' : Real) :
    isingRadialGridCellPoint mesh i j x y -
        isingRadialGridCellPoint mesh i j x' y' =
      (mesh : Complex) *
        ⟨((x - x') + (y - y')) / 2,
          ((x - x') - (y - y')) / 2⟩ := by
  apply Complex.ext <;>
    simp [isingRadialGridCellPoint] <;> ring


theorem abs_mesh_mul_cellCoordinate_l1_le_four_dist
    (mesh : Real) (i j : Nat) (x x' y y' : Real) :
    |mesh| * (|x - x'| + |y - y'|) ≤
      4 * dist (isingRadialGridCellPoint mesh i j x y)
        (isingRadialGridCellPoint mesh i j x' y') := by
  let z := isingRadialGridCellPoint mesh i j x y -
    isingRadialGridCellPoint mesh i j x' y'
  have hzre : z.re = mesh * ((x - x') + (y - y')) / 2 := by
    rw [show z = (mesh : Complex) *
        ⟨((x - x') + (y - y')) / 2,
          ((x - x') - (y - y')) / 2⟩ by
      exact isingRadialGridCellPoint_sub mesh i j x x' y y']
    simp
    ring
  have hzim : z.im = mesh * ((x - x') - (y - y')) / 2 := by
    rw [show z = (mesh : Complex) *
        ⟨((x - x') + (y - y')) / 2,
          ((x - x') - (y - y')) / 2⟩ by
      exact isingRadialGridCellPoint_sub mesh i j x x' y y']
    simp
    ring
  have hxident : mesh * (x - x') = z.re + z.im := by
    rw [hzre, hzim]
    ring
  have hyident : mesh * (y - y') = z.re - z.im := by
    rw [hzre, hzim]
    ring
  have hxbound : |mesh| * |x - x'| ≤ 2 * ‖z‖ := by
    rw [← abs_mul, hxident]
    calc
      |z.re + z.im| ≤ |z.re| + |z.im| := abs_add_le _ _
      _ ≤ ‖z‖ + ‖z‖ :=
        add_le_add (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z)
      _ = 2 * ‖z‖ := by ring
  have hybound : |mesh| * |y - y'| ≤ 2 * ‖z‖ := by
    rw [← abs_mul, hyident]
    calc
      |z.re - z.im| ≤ |z.re| + |z.im| := abs_sub _ _
      _ ≤ ‖z‖ + ‖z‖ :=
        add_le_add (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z)
      _ = 2 * ‖z‖ := by ring
  rw [mul_add]
  calc
    |mesh| * |x - x'| + |mesh| * |y - y'| ≤
        2 * ‖z‖ + 2 * ‖z‖ := add_le_add hxbound hybound
    _ = 4 * dist (isingRadialGridCellPoint mesh i j x y)
        (isingRadialGridCellPoint mesh i j x' y') := by
      rw [dist_eq_norm]
      change 2 * ‖z‖ + 2 * ‖z‖ = 4 * ‖z‖
      ring


end
end StatMech.Universality
