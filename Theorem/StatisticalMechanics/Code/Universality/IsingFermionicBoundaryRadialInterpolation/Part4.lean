/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem complexBilinearCell_norm_sub_le
    (a00 a10 a01 a11 : Complex) (x x' y y' D : Real)
    (hx0' : 0 ≤ x') (hx1' : x' ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hbottom : ‖a10 - a00‖ ≤ D) (htop : ‖a11 - a01‖ ≤ D)
    (hleft : ‖a01 - a00‖ ≤ D) (hright : ‖a11 - a10‖ ≤ D) :
    ‖complexBilinearCell a00 a10 a01 a11 x y -
      complexBilinearCell a00 a10 a01 a11 x' y'‖ ≤
      D * (|x - x'| + |y - y'|) := by
  have hxident : complexBilinearCell a00 a10 a01 a11 x y -
        complexBilinearCell a00 a10 a01 a11 x' y =
      ((x - x' : Real) : Complex) *
        (((1 - y : Real) : Complex) * (a10 - a00) +
          ((y : Real) : Complex) * (a11 - a01)) := by
    unfold complexBilinearCell
    push_cast
    ring
  have hyident : complexBilinearCell a00 a10 a01 a11 x' y -
        complexBilinearCell a00 a10 a01 a11 x' y' =
      ((y - y' : Real) : Complex) *
        (((1 - x' : Real) : Complex) * (a01 - a00) +
          ((x' : Real) : Complex) * (a11 - a10)) := by
    unfold complexBilinearCell
    push_cast
    ring
  have hxbound : ‖complexBilinearCell a00 a10 a01 a11 x y -
        complexBilinearCell a00 a10 a01 a11 x' y‖ ≤ D * |x - x'| := by
    rw [hxident, norm_mul]
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1y : |1 - y| = 1 - y := abs_of_nonneg (by linarith)
    have hy : |y| = y := abs_of_nonneg hy0
    have hnorm1y : ‖((1 - y : Real) : Complex)‖ = 1 - y := by
      rw [Complex.norm_real, Real.norm_eq_abs, h1y]
    have hnormy : ‖((y : Real) : Complex)‖ = y := by
      rw [Complex.norm_real, Real.norm_eq_abs, hy]
    calc
      |x - x'| * ‖((1 - y : Real) : Complex) * (a10 - a00) +
          ((y : Real) : Complex) * (a11 - a01)‖ ≤
        |x - x'| * (‖((1 - y : Real) : Complex) * (a10 - a00)‖ +
          ‖((y : Real) : Complex) * (a11 - a01)‖) := by
            gcongr
            exact norm_add_le _ _
      _ = |x - x'| * ((1 - y) * ‖a10 - a00‖ +
          y * ‖a11 - a01‖) := by
        rw [norm_mul, norm_mul, hnorm1y, hnormy]
      _ ≤ |x - x'| * ((1 - y) * D + y * D) := by gcongr
      _ = D * |x - x'| := by ring
  have hybound : ‖complexBilinearCell a00 a10 a01 a11 x' y -
        complexBilinearCell a00 a10 a01 a11 x' y'‖ ≤ D * |y - y'| := by
    rw [hyident, norm_mul]
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1x : |1 - x'| = 1 - x' := abs_of_nonneg (by linarith)
    have hx : |x'| = x' := abs_of_nonneg hx0'
    have hnorm1x : ‖((1 - x' : Real) : Complex)‖ = 1 - x' := by
      rw [Complex.norm_real, Real.norm_eq_abs, h1x]
    have hnormx : ‖((x' : Real) : Complex)‖ = x' := by
      rw [Complex.norm_real, Real.norm_eq_abs, hx]
    calc
      |y - y'| * ‖((1 - x' : Real) : Complex) * (a01 - a00) +
          ((x' : Real) : Complex) * (a11 - a10)‖ ≤
        |y - y'| * (‖((1 - x' : Real) : Complex) * (a01 - a00)‖ +
          ‖((x' : Real) : Complex) * (a11 - a10)‖) := by
            gcongr
            exact norm_add_le _ _
      _ = |y - y'| * ((1 - x') * ‖a01 - a00‖ +
          x' * ‖a11 - a10‖) := by
        rw [norm_mul, norm_mul, hnorm1x, hnormx]
      _ ≤ |y - y'| * ((1 - x') * D + x' * D) := by gcongr
      _ = D * |y - y'| := by ring
  calc
    ‖complexBilinearCell a00 a10 a01 a11 x y -
        complexBilinearCell a00 a10 a01 a11 x' y'‖ ≤
      ‖complexBilinearCell a00 a10 a01 a11 x y -
          complexBilinearCell a00 a10 a01 a11 x' y‖ +
        ‖complexBilinearCell a00 a10 a01 a11 x' y -
          complexBilinearCell a00 a10 a01 a11 x' y'‖ := by
      rw [show complexBilinearCell a00 a10 a01 a11 x y -
          complexBilinearCell a00 a10 a01 a11 x' y' =
        (complexBilinearCell a00 a10 a01 a11 x y -
          complexBilinearCell a00 a10 a01 a11 x' y) +
        (complexBilinearCell a00 a10 a01 a11 x' y -
          complexBilinearCell a00 a10 a01 a11 x' y') by ring]
      exact norm_add_le _ _
    _ ≤ D * |x - x'| + D * |y - y'| := add_le_add hxbound hybound
    _ = _ := by ring


theorem isingRadialGridPosition_eq_scaledCarrierPosition
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (mesh : Real) (i j : Fin m) (s : FKIsingMedialSide) :
    isingRadialGridPosition mesh i.1 j.1 =
      (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn
        (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) := by
  unfold isingRadialGridPosition
  congr 1
  change _ = (fkIsingSquareSitePosition
      (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm i j)).tail.1 +
    fkIsingSquareSitePosition
      (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm i j)).head.1) / 2
  by_cases h : Even (i.1 + j.1)
  · rw [fkIsingSquareRadialPatchEdge_eq_east n m hm i j h]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    simp [
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareSitePosition,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
    have hmod := Nat.even_iff.mp h
    have hqNat : 2 * ((i.1 + j.1 + 1) / 2) = i.1 + j.1 := by omega
    have hq : (2 : Real) * (((i.1 + j.1 + 1) / 2 : Nat) : Real) =
        (i.1 : Real) + (j.1 : Real) := by exact_mod_cast hqNat
    have hdivInt :
        ((i.1 : Int) + (j.1 : Int) + 1) / 2 =
          (((i.1 + j.1 + 1) / 2 : Nat) : Int) := by
      omega
    have hdivReal :
        ((((i.1 : Int) + (j.1 : Int) + 1) / 2 : Int) : Real) =
          (((i.1 + j.1 + 1) / 2 : Nat) : Real) := by
      norm_cast
    apply Complex.ext <;> simp
    all_goals rw [hdivReal]
    all_goals linarith
  · rw [fkIsingSquareRadialPatchEdge_eq_north n m hm i j h]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    simp [
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareSitePosition,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
    have hmod := Nat.not_even_iff.mp h
    have hqNat : 2 * ((i.1 + j.1 + 1) / 2) = i.1 + j.1 + 1 := by omega
    have hq : (2 : Real) * (((i.1 + j.1 + 1) / 2 : Nat) : Real) =
        (i.1 : Real) + (j.1 : Real) + 1 := by exact_mod_cast hqNat
    have hdivInt :
        ((i.1 : Int) + (j.1 : Int) + 1) / 2 =
          (((i.1 + j.1 + 1) / 2 : Nat) : Int) := by
      omega
    have hdivReal :
        ((((i.1 : Int) + (j.1 : Int) + 1) / 2 : Int) : Real) =
          (((i.1 + j.1 + 1) / 2 : Nat) : Real) := by
      norm_cast
    apply Complex.ext <;> simp
    all_goals rw [hdivReal]
    all_goals linarith


end
end StatMech.Universality
