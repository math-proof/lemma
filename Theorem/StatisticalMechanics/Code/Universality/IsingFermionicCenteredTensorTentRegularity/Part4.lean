/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Mathlib.Topology.UnitInterval
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity.Part3


namespace StatMech.Universality

open Metric Set

open scoped unitInterval

noncomputable section

theorem complexBilinearTwoByTwo_norm_sub_le
    (a00 a10 a20 a01 a11 a21 a02 a12 a22 : Complex)
    (x x' y y' D : Real)
    (hx0 : 0 <= x) (hx2 : x <= 2)
    (hx0' : 0 <= x') (hx2' : x' <= 2)
    (hy0 : 0 <= y) (hy2 : y <= 2)
    (hy0' : 0 <= y') (hy2' : y' <= 2)
    (h00_10 : norm (a10 - a00) <= D)
    (h10_20 : norm (a20 - a10) <= D)
    (h01_11 : norm (a11 - a01) <= D)
    (h11_21 : norm (a21 - a11) <= D)
    (h02_12 : norm (a12 - a02) <= D)
    (h12_22 : norm (a22 - a12) <= D)
    (h00_01 : norm (a01 - a00) <= D)
    (h01_02 : norm (a02 - a01) <= D)
    (h10_11 : norm (a11 - a10) <= D)
    (h11_12 : norm (a12 - a11) <= D)
    (h20_21 : norm (a21 - a20) <= D)
    (h21_22 : norm (a22 - a21) <= D) :
    norm (complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x y -
        complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y') <=
      D * (|x - x'| + |y - y'|) := by
  have hhorizontal :
      norm (complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x y -
        complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y) <=
        D * |x - x'| := by
    by_cases hy : y <= 1
    · simpa [complexBilinearTwoByTwo, hy] using
        complexBilinearHorizontalStrip_norm_sub_le
          a00 a10 a20 a01 a11 a21 x x' y D
          hx0 hx2 hx0' hx2' hy0 hy h00_10 h10_20 h01_11 h11_21
          h00_01 h10_11 h20_21
    · have hy1 : 1 < y := lt_of_not_ge hy
      simpa [complexBilinearTwoByTwo, hy] using
        complexBilinearHorizontalStrip_norm_sub_le
          a01 a11 a21 a02 a12 a22 x x' (y - 1) D
          hx0 hx2 hx0' hx2' (by linarith) (by linarith)
          h01_11 h11_21 h02_12 h12_22 h01_02 h11_12 h21_22
  have hvertical :
      norm (complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y -
        complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y') <=
        D * |y - y'| := by
    by_cases hx' : x' <= 1
    · simpa [complexBilinearTwoByTwo, complexBilinearHorizontalStrip, hx'] using
        complexBilinearVerticalStrip_norm_sub_le
          a00 a10 a01 a11 a02 a12 x' y y' D
          hx0' hx' hy0 hy2 hy0' hy2'
          h00_10 h01_11 h02_12 h00_01 h01_02 h10_11 h11_12
    · have hx'1 : 1 < x' := lt_of_not_ge hx'
      simpa [complexBilinearTwoByTwo, complexBilinearHorizontalStrip, hx'] using
        complexBilinearVerticalStrip_norm_sub_le
          a10 a20 a11 a21 a12 a22 (x' - 1) y y' D
          (by linarith) (by linarith) hy0 hy2 hy0' hy2'
          h10_20 h11_21 h12_22 h10_11 h11_12 h20_21 h21_22
  calc
    norm (complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x y -
        complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y') <=
      norm (complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x y -
        complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y) +
      norm (complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y -
        complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y') := by
      rw [show complexBilinearTwoByTwo
            a00 a10 a20 a01 a11 a21 a02 a12 a22 x y -
          complexBilinearTwoByTwo
            a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y' =
        (complexBilinearTwoByTwo
            a00 a10 a20 a01 a11 a21 a02 a12 a22 x y -
          complexBilinearTwoByTwo
            a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y) +
        (complexBilinearTwoByTwo
            a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y -
          complexBilinearTwoByTwo
            a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y') by ring]
      exact norm_add_le _ _
    _ <= D * |x - x'| + D * |y - y'| :=
      add_le_add hhorizontal hvertical
    _ = D * (|x - x'| + |y - y'|) := by ring


theorem finiteCenteredRadialGridInterpolant_horizontalBoundary
    (n : Nat) (mesh : Real)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (y : Real) :
    finiteCenteredRadialGridInterpolant n mesh value
        (isingCenteredRadialGridCellPoint mesh n i j 1 y) =
      finiteCenteredRadialGridInterpolant n mesh value
        (isingCenteredRadialGridCellPoint mesh n (i + 1) j 0 y) := by
  apply congrArg (finiteCenteredRadialGridInterpolant n mesh value)
  unfold isingCenteredRadialGridCellPoint isingRadialGridCellPoint
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring


theorem finiteCenteredRadialGridInterpolant_verticalBoundary
    (n : Nat) (mesh : Real)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (x : Real) :
    finiteCenteredRadialGridInterpolant n mesh value
        (isingCenteredRadialGridCellPoint mesh n i j x 1) =
      finiteCenteredRadialGridInterpolant n mesh value
        (isingCenteredRadialGridCellPoint mesh n i (j + 1) x 0) := by
  apply congrArg (finiteCenteredRadialGridInterpolant n mesh value)
  unfold isingCenteredRadialGridCellPoint isingRadialGridCellPoint
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring


theorem isingCenteredRadialGridCellPoint_add_one_x
    (mesh : Real) (n i j : Nat) (x y : Real) :
    isingCenteredRadialGridCellPoint mesh n i j (1 + x) y =
      isingCenteredRadialGridCellPoint mesh n (i + 1) j x y := by
  unfold isingCenteredRadialGridCellPoint isingRadialGridCellPoint
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring


theorem isingCenteredRadialGridCellPoint_add_one_y
    (mesh : Real) (n i j : Nat) (x y : Real) :
    isingCenteredRadialGridCellPoint mesh n i j x (1 + y) =
      isingCenteredRadialGridCellPoint mesh n i (j + 1) x y := by
  unfold isingCenteredRadialGridCellPoint isingRadialGridCellPoint
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring


theorem finiteCenteredRadialGridInterpolant_twoByTwo
    (n : Nat) (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (hi : i + 2 < 2 * n) (hj : j + 2 < 2 * n)
    (x y : Real) (hx0 : 0 <= x) (hx2 : x <= 2)
    (hy0 : 0 <= y) (hy2 : y <= 2) :
    finiteCenteredRadialGridInterpolant n mesh value
        (isingCenteredRadialGridCellPoint mesh n i j x y) =
      complexBilinearTwoByTwo
        (value ⟨i, by omega⟩ ⟨j, by omega⟩)
        (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩)
        (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩)
        (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩)
        (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩)
        (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩)
        (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩)
        (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩)
        (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩) x y := by
  by_cases hx : x <= 1
  · by_cases hy : y <= 1
    · rw [finiteCenteredRadialGridInterpolant_cellPoint
        n mesh hmesh value i j (by omega) (by omega) x y
        hx0 hx hy0 hy]
      simp [complexBilinearTwoByTwo, complexBilinearHorizontalStrip, hx, hy]
    · have hy1 : 1 < y := lt_of_not_ge hy
      rw [show isingCenteredRadialGridCellPoint mesh n i j x y =
          isingCenteredRadialGridCellPoint mesh n i (j + 1) x (y - 1) by
        convert isingCenteredRadialGridCellPoint_add_one_y
          mesh n i j x (y - 1) using 1 <;> ring]
      rw [finiteCenteredRadialGridInterpolant_cellPoint
        n mesh hmesh value i (j + 1) (by omega) (by omega) x (y - 1)
        hx0 hx (by linarith) (by linarith)]
      simp [complexBilinearTwoByTwo, complexBilinearHorizontalStrip, hx, hy]
  · have hx1 : 1 < x := lt_of_not_ge hx
    by_cases hy : y <= 1
    · rw [show isingCenteredRadialGridCellPoint mesh n i j x y =
          isingCenteredRadialGridCellPoint mesh n (i + 1) j (x - 1) y by
        convert isingCenteredRadialGridCellPoint_add_one_x
          mesh n i j (x - 1) y using 1 <;> ring]
      rw [finiteCenteredRadialGridInterpolant_cellPoint
        n mesh hmesh value (i + 1) j (by omega) (by omega) (x - 1) y
        (by linarith) (by linarith) hy0 hy]
      simp [complexBilinearTwoByTwo, complexBilinearHorizontalStrip, hx, hy]
    · have hy1 : 1 < y := lt_of_not_ge hy
      rw [show isingCenteredRadialGridCellPoint mesh n i j x y =
          isingCenteredRadialGridCellPoint mesh n (i + 1) (j + 1)
            (x - 1) (y - 1) by
        calc
          isingCenteredRadialGridCellPoint mesh n i j x y =
              isingCenteredRadialGridCellPoint mesh n i j x (1 + (y - 1)) := by
            congr 2
            ring
          _ = isingCenteredRadialGridCellPoint mesh n i (j + 1) x (y - 1) :=
            isingCenteredRadialGridCellPoint_add_one_y
              mesh n i j x (y - 1)
          _ = isingCenteredRadialGridCellPoint mesh n (i + 1) (j + 1)
              (x - 1) (y - 1) := by
            rw [← isingCenteredRadialGridCellPoint_add_one_x
              mesh n i (j + 1) (x - 1) (y - 1)]
            congr 2
            ring]
      rw [finiteCenteredRadialGridInterpolant_cellPoint
        n mesh hmesh value (i + 1) (j + 1) (by omega) (by omega)
        (x - 1) (y - 1) (by linarith) (by linarith)
        (by linarith) (by linarith)]
      simp [complexBilinearTwoByTwo, complexBilinearHorizontalStrip, hx, hy]


theorem finiteCenteredRadialGridInterpolant_twoByTwo_norm_sub_le_dist
    (n : Nat) (mesh : Real) (hmesh : 0 < mesh)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (hi : i + 2 < 2 * n) (hj : j + 2 < 2 * n)
    (x x' y y' L : Real)
    (hx0 : 0 <= x) (hx2 : x <= 2)
    (hx0' : 0 <= x') (hx2' : x' <= 2)
    (hy0 : 0 <= y) (hy2 : y <= 2)
    (hy0' : 0 <= y') (hy2' : y' <= 2)
    (hL : 0 <= L)
    (h00_10 : norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ -
      value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (h10_20 : norm (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩ -
      value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (h01_11 : norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
      value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (h11_21 : norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ -
      value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (h02_12 : norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ -
      value ⟨i, by omega⟩ ⟨j + 2, by omega⟩) <= mesh * L)
    (h12_22 : norm (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ -
      value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩) <= mesh * L)
    (h00_01 : norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ -
      value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (h01_02 : norm (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩ -
      value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (h10_11 : norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
      value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (h11_12 : norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ -
      value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (h20_21 : norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ -
      value ⟨i + 2, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (h21_22 : norm (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ -
      value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L) :
    norm (finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x y) -
        finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x' y')) <=
      4 * L * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n i j x' y') := by
  rw [finiteCenteredRadialGridInterpolant_twoByTwo n mesh hmesh.ne' value
      i j hi hj x y hx0 hx2 hy0 hy2,
    finiteCenteredRadialGridInterpolant_twoByTwo n mesh hmesh.ne' value
      i j hi hj x' y' hx0' hx2' hy0' hy2']
  have hpatch := complexBilinearTwoByTwo_norm_sub_le
    (value ⟨i, by omega⟩ ⟨j, by omega⟩)
    (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩)
    (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩)
    (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩)
    (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩)
    (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩)
    (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩)
    (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩)
    (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩)
    x x' y y' (mesh * L) hx0 hx2 hx0' hx2' hy0 hy2 hy0' hy2'
    h00_10 h10_20 h01_11 h11_21 h02_12 h12_22
    h00_01 h01_02 h10_11 h11_12 h20_21 h21_22
  have hgeom := abs_mesh_mul_cellCoordinate_l1_le_four_dist
    mesh i j x x' y y'
  have ht : mesh * (|x - x'| + |y - y'|) <=
      4 * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n i j x' y') := by
    simpa [abs_of_pos hmesh, isingCenteredRadialGridCellPoint,
      dist_eq_norm] using hgeom
  calc
    norm (complexBilinearTwoByTwo
          (value ⟨i, by omega⟩ ⟨j, by omega⟩)
          (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩)
          (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩)
          (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩)
          (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩)
          (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩)
          (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩)
          (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩)
          (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩) x y -
        complexBilinearTwoByTwo
          (value ⟨i, by omega⟩ ⟨j, by omega⟩)
          (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩)
          (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩)
          (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩)
          (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩)
          (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩)
          (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩)
          (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩)
          (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩) x' y') <=
        (mesh * L) * (|x - x'| + |y - y'|) := hpatch
    _ = L * (mesh * (|x - x'| + |y - y'|)) := by ring
    _ <= L * (4 * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n i j x' y')) := by
      exact mul_le_mul_of_nonneg_left ht hL
    _ = 4 * L * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n i j x' y') := by ring


theorem finiteCenteredRadialGridInterpolant_horizontalAdjacent_norm_sub_le
    (n : Nat) (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (hi : i + 2 < 2 * n) (hj : j + 1 < 2 * n)
    (x x' y y' D : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (haBottom :
      norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= D)
    (haTop :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= D)
    (haLeft :
      norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= D)
    (haRight :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= D)
    (hbBottom :
      norm (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= D)
    (hbTop :
      norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= D)
    (hbRight :
      norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 2, by omega⟩ ⟨j, by omega⟩) <= D) :
    norm (finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x y) -
        finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y')) <=
      D * ((1 - x) + x' + |y - y'|) := by
  rw [finiteCenteredRadialGridInterpolant_cellPoint
      n mesh hmesh value i j (by omega) hj x y hx0 hx1 hy0 hy1,
    finiteCenteredRadialGridInterpolant_cellPoint
      n mesh hmesh value (i + 1) j (by omega) hj x' y'
        hx0' hx1' hy0' hy1']
  exact complexBilinearCell_horizontalAdjacent_norm_sub_le
    _ _ _ _ _ _ x x' y y' D hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'
      haBottom haTop haLeft haRight hbBottom hbTop hbRight


theorem finiteCenteredRadialGridInterpolant_verticalAdjacent_norm_sub_le
    (n : Nat) (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (hi : i + 1 < 2 * n) (hj : j + 2 < 2 * n)
    (x x' y y' D : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (haBottom :
      norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= D)
    (haTop :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= D)
    (haLeft :
      norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= D)
    (haRight :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= D)
    (hbTop :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 2, by omega⟩) <= D)
    (hbLeft :
      norm (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= D)
    (hbRight :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= D) :
    norm (finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x y) -
        finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y')) <=
      D * (|x - x'| + (1 - y) + y') := by
  rw [finiteCenteredRadialGridInterpolant_cellPoint
      n mesh hmesh value i j hi (by omega) x y hx0 hx1 hy0 hy1,
    finiteCenteredRadialGridInterpolant_cellPoint
      n mesh hmesh value i (j + 1) hi (by omega) x' y'
        hx0' hx1' hy0' hy1']
  exact complexBilinearCell_verticalAdjacent_norm_sub_le
    _ _ _ _ _ _ x x' y y' D hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'
      haBottom haTop haLeft haRight hbTop hbLeft hbRight


theorem finiteCenteredRadialGridInterpolant_horizontalAdjacent_norm_sub_le_dist
    (n : Nat) (mesh : Real) (hmesh : 0 < mesh)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (hi : i + 2 < 2 * n) (hj : j + 1 < 2 * n)
    (x x' y y' L : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (hL : 0 <= L)
    (haBottom :
      norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (haTop :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (haLeft :
      norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (haRight :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (hbBottom :
      norm (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (hbTop :
      norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (hbRight :
      norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 2, by omega⟩ ⟨j, by omega⟩) <= mesh * L) :
    norm (finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x y) -
        finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y')) <=
      4 * L * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y') := by
  have hosc :=
    finiteCenteredRadialGridInterpolant_horizontalAdjacent_norm_sub_le
      n mesh hmesh.ne' value i j hi hj x x' y y' (mesh * L)
      hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'
      haBottom haTop haLeft haRight hbBottom hbTop hbRight
  have hgeom := abs_mesh_mul_cellCoordinate_l1_le_four_dist
    mesh i j x (1 + x') y y'
  have hpoint :
      isingCenteredRadialGridCellPoint mesh n i j (1 + x') y' =
        isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y' := by
    unfold isingCenteredRadialGridCellPoint isingRadialGridCellPoint
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
      push_cast
      ring
    · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im]
      push_cast
      ring
  have ht :
      mesh * ((1 - x) + x' + |y - y'|) <=
        4 * dist
          (isingCenteredRadialGridCellPoint mesh n i j x y)
          (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y') := by
    rw [← hpoint]
    calc
      mesh * ((1 - x) + x' + |y - y'|) =
          |mesh| * (|x - (1 + x')| + |y - y'|) := by
        rw [abs_of_pos hmesh,
          abs_of_nonpos (by linarith : x - (1 + x') <= 0)]
        ring
      _ <= 4 * dist
          (isingRadialGridCellPoint mesh i j x y)
          (isingRadialGridCellPoint mesh i j (1 + x') y') := hgeom
      _ = 4 * dist
          (isingCenteredRadialGridCellPoint mesh n i j x y)
          (isingCenteredRadialGridCellPoint mesh n i j (1 + x') y') := by
        unfold isingCenteredRadialGridCellPoint
        rw [dist_eq_norm, dist_eq_norm]
        congr 2
        ring
  calc
    norm (finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x y) -
        finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y')) <=
      (mesh * L) * ((1 - x) + x' + |y - y'|) := hosc
    _ = L * (mesh * ((1 - x) + x' + |y - y'|)) := by ring
    _ <= L * (4 * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y')) := by
      gcongr
    _ = 4 * L * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y') := by ring


theorem finiteCenteredRadialGridInterpolant_verticalAdjacent_norm_sub_le_dist
    (n : Nat) (mesh : Real) (hmesh : 0 < mesh)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (hi : i + 1 < 2 * n) (hj : j + 2 < 2 * n)
    (x x' y y' L : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (hL : 0 <= L)
    (haBottom :
      norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (haTop :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (haLeft :
      norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (haRight :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (hbTop :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 2, by omega⟩) <= mesh * L)
    (hbLeft :
      norm (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (hbRight :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L) :
    norm (finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x y) -
        finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y')) <=
      4 * L * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y') := by
  have hosc :=
    finiteCenteredRadialGridInterpolant_verticalAdjacent_norm_sub_le
      n mesh hmesh.ne' value i j hi hj x x' y y' (mesh * L)
      hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'
      haBottom haTop haLeft haRight hbTop hbLeft hbRight
  have hgeom := abs_mesh_mul_cellCoordinate_l1_le_four_dist
    mesh i j x x' y (1 + y')
  have hpoint :
      isingCenteredRadialGridCellPoint mesh n i j x' (1 + y') =
        isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y' := by
    unfold isingCenteredRadialGridCellPoint isingRadialGridCellPoint
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
      push_cast
      ring
    · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im]
      push_cast
      ring
  have ht :
      mesh * (|x - x'| + (1 - y) + y') <=
        4 * dist
          (isingCenteredRadialGridCellPoint mesh n i j x y)
          (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y') := by
    rw [← hpoint]
    calc
      mesh * (|x - x'| + (1 - y) + y') =
          |mesh| * (|x - x'| + |y - (1 + y')|) := by
        rw [abs_of_pos hmesh,
          abs_of_nonpos (by linarith : y - (1 + y') <= 0)]
        ring
      _ <= 4 * dist
          (isingRadialGridCellPoint mesh i j x y)
          (isingRadialGridCellPoint mesh i j x' (1 + y')) := hgeom
      _ = 4 * dist
          (isingCenteredRadialGridCellPoint mesh n i j x y)
          (isingCenteredRadialGridCellPoint mesh n i j x' (1 + y')) := by
        unfold isingCenteredRadialGridCellPoint
        rw [dist_eq_norm, dist_eq_norm]
        congr 2
        ring
  calc
    norm (finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x y) -
        finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y')) <=
      (mesh * L) * (|x - x'| + (1 - y) + y') := hosc
    _ = L * (mesh * (|x - x'| + (1 - y) + y')) := by ring
    _ <= L * (4 * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y')) := by
      gcongr
    _ = 4 * L * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y') := by ring


end
end StatMech.Universality
