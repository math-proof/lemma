/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryScaledDomain.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3


namespace StatMech.Universality

open Filter Set Topology Metric

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

theorem natAbs_le_of_int_bounds {n : Nat} {z : Int}
    (h0 : -(n : Int) ≤ z) (h1 : z ≤ (n : Int)) : z.natAbs ≤ n := by
  have h : |z| ≤ (n : Int) := abs_le.mpr ⟨h0, h1⟩
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h


theorem exists_fkIsingSquareWiredCarrier_scaledPosition_near
    (n : Nat) (hn : 0 < n) (scale : Real) (hscale : 0 < scale)
    (z : Complex)
    (hx0 : -(n : Int) ≤ ⌊z.re / scale⌋)
    (hx1 : ⌊z.re / scale⌋ < (n : Int))
    (hy0 : -(n : Int) ≤ ⌊z.im / scale⌋)
    (hy1 : ⌊z.im / scale⌋ ≤ (n : Int)) :
    ∃ a : FKIsingSquareWiredCarrier n,
      dist z ((scale : Complex) *
        fkIsingSquareWiredCarrierPosition n hn a) < 3 * scale := by
  let x : Int := ⌊z.re / scale⌋
  let y : Int := ⌊z.im / scale⌋
  let u : (fkSquareBoxPlanar n).V :=
    ⟨![x, y], by
      intro k
      fin_cases k
      · change x.natAbs ≤ n
        apply natAbs_le_of_int_bounds
        · simpa [x] using hx0
        · have hx1' : x < (n : Int) := by simpa [x] using hx1
          omega
      · change y.natAbs ≤ n
        exact natAbs_le_of_int_bounds (by simpa [y] using hy0)
          (by simpa [y] using hy1)⟩
  have heast : fkIsingSquareDirectionAvailable n u .east := by
    simp [fkIsingSquareDirectionAvailable, u]
    omega
  let e := fkIsingSquareDirectionEdge n u .east heast
  let a : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let w : Complex :=
    (scale * ((x : Real) + 1 / 2) : Real) +
      Complex.I * (scale * (y : Real) : Real)
  have hposition :
      (scale : Complex) * fkIsingSquareWiredCarrierPosition n hn a = w := by
    simp [a, e, fkIsingSquareWiredCarrierPosition,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareSitePosition, u, w]
    push_cast
    ring
  have hxfloor : (x : Real) ≤ z.re / scale := by
    exact_mod_cast Int.floor_le (z.re / scale)
  have hxceil : z.re / scale < (x : Real) + 1 := by
    exact_mod_cast Int.lt_floor_add_one (z.re / scale)
  have hyfloor : (y : Real) ≤ z.im / scale := by
    exact_mod_cast Int.floor_le (z.im / scale)
  have hyceil : z.im / scale < (y : Real) + 1 := by
    exact_mod_cast Int.lt_floor_add_one (z.im / scale)
  have hxabs : |z.re - scale * ((x : Real) + 1 / 2)| ≤ scale / 2 := by
    rw [abs_le]
    constructor <;> (field_simp at hxfloor hxceil ⊢ <;> nlinarith)
  have hyabs : |z.im - scale * (y : Real)| < scale := by
    rw [abs_lt]
    constructor <;> (field_simp at hyfloor hyceil ⊢ <;> nlinarith)
  refine ⟨a, ?_⟩
  rw [hposition, dist_eq_norm]
  calc
    ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |z.re - scale * ((x : Real) + 1 / 2)| +
        |z.im - scale * (y : Real)| := by simp [w]
    _ < scale / 2 + scale := add_lt_add_of_le_of_lt hxabs hyabs
    _ < 3 * scale := by linarith


end
end StatMech.Universality
