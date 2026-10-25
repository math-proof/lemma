/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part14


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem reflectedRadialAxisFloor_box
    (n : Nat) (mesh x y : Real) (hmesh : 0 < mesh)
    (hinside : |x| + |y| + 3 * mesh ≤ mesh * n) :
    0 ≤ (n : Int) + ⌊x / mesh - 1 / 2⌋ - ⌊y / mesh⌋ ∧
      0 ≤ (n : Int) + ⌊x / mesh - 1 / 2⌋ + ⌊y / mesh⌋ ∧
      ⌊x / mesh - 1 / 2⌋ - ⌊y / mesh⌋ + 1 < (n : Int) ∧
      ⌊x / mesh - 1 / 2⌋ + ⌊y / mesh⌋ + 1 < (n : Int) := by
  let qx : Int := ⌊x / mesh - 1 / 2⌋
  let qy : Int := ⌊y / mesh⌋
  have hinside' : |x| / mesh + |y| / mesh + 3 ≤ (n : Real) := by
    have hdiv : (|x| + |y| + 3 * mesh) / mesh ≤ (n : Real) :=
      (div_le_iff₀ hmesh).2 (by nlinarith)
    convert hdiv using 1 <;> field_simp <;> ring
  have hxlo : -(|x| / mesh) ≤ x / mesh := by
    simpa only [neg_div] using
      div_le_div_of_nonneg_right (neg_abs_le x) hmesh.le
  have hxhi : x / mesh ≤ |x| / mesh := by
    exact div_le_div_of_nonneg_right (le_abs_self x) hmesh.le
  have hylo : -(|y| / mesh) ≤ y / mesh := by
    simpa only [neg_div] using
      div_le_div_of_nonneg_right (neg_abs_le y) hmesh.le
  have hyhi : y / mesh ≤ |y| / mesh := by
    exact div_le_div_of_nonneg_right (le_abs_self y) hmesh.le
  have hqxlo : x / mesh - 1 / 2 < (qx : Real) + 1 := by
    exact_mod_cast Int.lt_floor_add_one (x / mesh - 1 / 2)
  have hqxhi : (qx : Real) ≤ x / mesh - 1 / 2 := by
    exact_mod_cast Int.floor_le (x / mesh - 1 / 2)
  have hqylo : y / mesh < (qy : Real) + 1 := by
    exact_mod_cast Int.lt_floor_add_one (y / mesh)
  have hqyhi : (qy : Real) ≤ y / mesh := by
    exact_mod_cast Int.floor_le (y / mesh)
  have hminusLower : 0 ≤ (n : Int) + qx - qy := by
    have hreal : 0 < (n : Real) + (qx : Real) - (qy : Real) := by
      nlinarith
    exact_mod_cast hreal.le
  have hplusLower : 0 ≤ (n : Int) + qx + qy := by
    have hreal : 0 < (n : Real) + (qx : Real) + (qy : Real) := by
      nlinarith
    exact_mod_cast hreal.le
  have hminusUpper : qx - qy + 1 < (n : Int) := by
    have hreal : (qx : Real) - (qy : Real) + 1 < (n : Real) := by
      nlinarith
    exact_mod_cast hreal
  have hplusUpper : qx + qy + 1 < (n : Int) := by
    have hreal : (qx : Real) + (qy : Real) + 1 < (n : Real) := by
      nlinarith
    exact_mod_cast hreal
  simpa [qx, qy] using
    And.intro hminusLower
      (And.intro hplusLower (And.intro hminusUpper hplusUpper))


theorem isingReflectedCenteredRadialGridPosition_snap
    (n : Nat) (mesh : Real) (z : Complex)
    (hi : 0 ≤ (n : Int) + ⌊z.re / mesh - 1 / 2⌋ - ⌊z.im / mesh⌋)
    (hj : 0 ≤ (n : Int) + ⌊z.re / mesh - 1 / 2⌋ + ⌊z.im / mesh⌋) :
    isingReflectedCenteredRadialGridPosition mesh n
        (reflectedRadialAxisSnapI n mesh z)
        (reflectedRadialAxisSnapJ n mesh z) =
      reflectedRadialAxisSnap mesh z := by
  let qx : Int := ⌊z.re / mesh - 1 / 2⌋
  let qy : Int := ⌊z.im / mesh⌋
  let ii : Int := (n : Int) + qx - qy
  let jj : Int := (n : Int) + qx + qy
  have hii : (ii.toNat : Int) = ii := Int.toNat_of_nonneg (by simpa [ii, qx, qy] using hi)
  have hjj : (jj.toNat : Int) = jj := Int.toNat_of_nonneg (by simpa [jj, qx, qy] using hj)
  have hiiR : (ii.toNat : Real) = (n : Real) + (qx : Real) - (qy : Real) := by
    exact_mod_cast hii
  have hjjR : (jj.toNat : Real) = (n : Real) + (qx : Real) + (qy : Real) := by
    exact_mod_cast hjj
  rw [isingReflectedCenteredRadialGridPosition_eq]
  unfold reflectedRadialAxisSnap shiftedRealGridFloor
  rw [show reflectedRadialAxisSnapI n mesh z = ii.toNat by rfl,
    show reflectedRadialAxisSnapJ n mesh z = jj.toNat by rfl]
  simp only [sub_zero]
  change
    (mesh * (((ii.toNat : Real) + (jj.toNat : Real) + 1) / 2 - n) : Real) +
        (mesh * (((jj.toNat : Real) - (ii.toNat : Real)) / 2) : Real) *
          Complex.I =
      (mesh * ((qx : Real) + 1 / 2) : Real) +
        (mesh * ((qy : Real) + 0) : Real) * Complex.I
  rw [hiiR, hjjR]
  ring


theorem isingReflectedCenteredRadialGridPosition_axisSnapBase
    (n : Nat) (mesh : Real) (z w : Complex)
    (hmesh : 0 < mesh) (him : z.im ≤ w.im)
    (hi0 : 0 ≤ (n : Int) + ⌊z.re / mesh - 1 / 2⌋ - ⌊w.im / mesh⌋)
    (hj0 : 0 ≤ (n : Int) + ⌊z.re / mesh - 1 / 2⌋ + ⌊z.im / mesh⌋) :
    isingReflectedCenteredRadialGridPosition mesh n
        (reflectedRadialAxisSnapBaseI n mesh z w +
          reflectedRadialAxisSnapHeight mesh z w)
        (reflectedRadialAxisSnapBaseJ n mesh z) =
      reflectedRadialAxisSnap mesh z := by
  let qx : Int := ⌊z.re / mesh - 1 / 2⌋
  let qyz : Int := ⌊z.im / mesh⌋
  let qyw : Int := ⌊w.im / mesh⌋
  have hqy : qyz ≤ qyw := by
    apply Int.floor_mono
    exact div_le_div_of_nonneg_right him hmesh.le
  have hdiff : 0 ≤ qyw - qyz := sub_nonneg.mpr hqy
  have hsum0 : 0 ≤ (n : Int) + qx - qyz := by
    have hbase : 0 ≤ (n : Int) + qx - qyw := by
      simpa [qx, qyw] using hi0
    omega
  have hIndex :
      reflectedRadialAxisSnapBaseI n mesh z w +
          reflectedRadialAxisSnapHeight mesh z w =
        reflectedRadialAxisSnapI n mesh z := by
    have hInt :
        (reflectedRadialAxisSnapBaseI n mesh z w : Int) +
            (reflectedRadialAxisSnapHeight mesh z w : Int) =
          (reflectedRadialAxisSnapI n mesh z : Int) := by
      rw [show (reflectedRadialAxisSnapBaseI n mesh z w : Int) =
          (n : Int) + qx - qyw by
        exact Int.toNat_of_nonneg (by simpa [qx, qyw] using hi0),
        show (reflectedRadialAxisSnapHeight mesh z w : Int) = qyw - qyz by
          simpa [reflectedRadialAxisSnapHeight, shiftedRealGridFloorSteps,
            qyw, qyz] using Int.toNat_of_nonneg hdiff,
        show (reflectedRadialAxisSnapI n mesh z : Int) =
            (n : Int) + qx - qyz by
          exact Int.toNat_of_nonneg hsum0]
      ring
    exact_mod_cast hInt
  rw [hIndex]
  apply isingReflectedCenteredRadialGridPosition_snap
  · simpa [qx, qyz] using hsum0
  · simpa [reflectedRadialAxisSnapBaseJ] using hj0


theorem fkIsingExpandingSquare_eventually_axisSnap_interior
    (z w : Complex) (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    ∀ᶠ k in atTop,
      0 ≤ (fkIsingExpandingSquareSide k : Int) +
          ⌊z.re / fkIsingExpandingSquareScale k - 1 / 2⌋ -
          ⌊w.im / fkIsingExpandingSquareScale k⌋ ∧
      0 ≤ (fkIsingExpandingSquareSide k : Int) +
          ⌊z.re / fkIsingExpandingSquareScale k - 1 / 2⌋ +
          ⌊z.im / fkIsingExpandingSquareScale k⌋ ∧
      reflectedRadialAxisSnapBaseI
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareScale k) z w +
          reflectedRadialAxisSnapWidth
            (fkIsingExpandingSquareScale k) z w +
          reflectedRadialAxisSnapHeight
            (fkIsingExpandingSquareScale k) z w + 1 <
        2 * fkIsingExpandingSquareSide k ∧
      reflectedRadialAxisSnapBaseJ
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareScale k) z +
          reflectedRadialAxisSnapWidth
            (fkIsingExpandingSquareScale k) z w +
          reflectedRadialAxisSnapHeight
            (fkIsingExpandingSquareScale k) z w + 1 <
        2 * fkIsingExpandingSquareSide k := by
  filter_upwards
    [fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior
      (|z.re| + |w.im|) 3,
    fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior
      (|z.re| + |z.im|) 3,
    fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior
      (|w.re| + |z.im|) 3,
    fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior
      (|w.re| + |w.im|) 3] with k hzw hzz hwz hww
  let n := fkIsingExpandingSquareSide k
  let mesh := fkIsingExpandingSquareScale k
  let qxz : Int := ⌊z.re / mesh - 1 / 2⌋
  let qxw : Int := ⌊w.re / mesh - 1 / 2⌋
  let qyz : Int := ⌊z.im / mesh⌋
  let qyw : Int := ⌊w.im / mesh⌋
  have hmesh : 0 < mesh := fkIsingExpandingSquareScale_pos k
  have hzw' : |z.re| + |w.im| + 3 * mesh ≤ mesh * n := by
    dsimp only [mesh, n]
    nlinarith
  have hzz' : |z.re| + |z.im| + 3 * mesh ≤ mesh * n := by
    dsimp only [mesh, n]
    nlinarith
  have hwz' : |w.re| + |z.im| + 3 * mesh ≤ mesh * n := by
    dsimp only [mesh, n]
    nlinarith
  have hww' : |w.re| + |w.im| + 3 * mesh ≤ mesh * n := by
    dsimp only [mesh, n]
    nlinarith
  have hboxZW := reflectedRadialAxisFloor_box n mesh z.re w.im hmesh hzw'
  have hboxZZ := reflectedRadialAxisFloor_box n mesh z.re z.im hmesh hzz'
  have hboxWZ := reflectedRadialAxisFloor_box n mesh w.re z.im hmesh hwz'
  have hboxWW := reflectedRadialAxisFloor_box n mesh w.re w.im hmesh hww'
  have hqx : qxz ≤ qxw := by
    apply Int.floor_mono
    exact sub_le_sub_right (div_le_div_of_nonneg_right hre hmesh.le) (1 / 2)
  have hqy : qyz ≤ qyw := by
    apply Int.floor_mono
    exact div_le_div_of_nonneg_right him hmesh.le
  have hi0 : 0 ≤ (n : Int) + qxz - qyw := by
    simpa [qxz, qyw] using hboxZW.1
  have hj0 : 0 ≤ (n : Int) + qxz + qyz := by
    simpa [qxz, qyz] using hboxZZ.2.1
  have hiUpper : qxw - qyz + 1 < (n : Int) := by
    simpa [qxw, qyz] using hboxWZ.2.2.1
  have hjUpper : qxw + qyw + 1 < (n : Int) := by
    simpa [qxw, qyw] using hboxWW.2.2.2
  have hbaseI :
      (reflectedRadialAxisSnapBaseI n mesh z w : Int) =
        (n : Int) + qxz - qyw := by
    exact Int.toNat_of_nonneg (by simpa [qxz, qyw] using hi0)
  have hbaseJ :
      (reflectedRadialAxisSnapBaseJ n mesh z : Int) =
        (n : Int) + qxz + qyz := by
    exact Int.toNat_of_nonneg (by simpa [qxz, qyz] using hj0)
  have hwidth :
      (reflectedRadialAxisSnapWidth mesh z w : Int) = qxw - qxz := by
    simpa [reflectedRadialAxisSnapWidth, shiftedRealGridFloorSteps,
      qxw, qxz] using Int.toNat_of_nonneg (sub_nonneg.mpr hqx)
  have hheight :
      (reflectedRadialAxisSnapHeight mesh z w : Int) = qyw - qyz := by
    simpa [reflectedRadialAxisSnapHeight, shiftedRealGridFloorSteps,
      qyw, qyz] using Int.toNat_of_nonneg (sub_nonneg.mpr hqy)
  have hiNat :
      reflectedRadialAxisSnapBaseI n mesh z w +
          reflectedRadialAxisSnapWidth mesh z w +
          reflectedRadialAxisSnapHeight mesh z w + 1 < 2 * n := by
    have hiInt :
        (reflectedRadialAxisSnapBaseI n mesh z w : Int) +
            (reflectedRadialAxisSnapWidth mesh z w : Int) +
            (reflectedRadialAxisSnapHeight mesh z w : Int) + 1 <
          2 * (n : Int) := by
      rw [hbaseI, hwidth, hheight]
      omega
    exact_mod_cast hiInt
  have hjNat :
      reflectedRadialAxisSnapBaseJ n mesh z +
          reflectedRadialAxisSnapWidth mesh z w +
          reflectedRadialAxisSnapHeight mesh z w + 1 < 2 * n := by
    have hjInt :
        (reflectedRadialAxisSnapBaseJ n mesh z : Int) +
            (reflectedRadialAxisSnapWidth mesh z w : Int) +
            (reflectedRadialAxisSnapHeight mesh z w : Int) + 1 <
          2 * (n : Int) := by
      rw [hbaseJ, hwidth, hheight]
      omega
    exact_mod_cast hjInt
  simpa [n, mesh, qxz, qyz] using
    And.intro hi0 (And.intro hj0 (And.intro hiNat hjNat))

theorem fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_continuous
    (k : Nat) :
    Continuous (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k) :=
  fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_continuous
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareMesh k)


theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral
    (n i j : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n) :
    complexDisplacementIntegral
        (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
          n hn gridScale normalizationScale)
        (isingReflectedCenteredRadialGridPosition gridScale n i j)
        ((gridScale : Complex) / 2 * (1 - Complex.I)) =
      ((fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
            ⟨i, by omega⟩ ⟨j, by omega⟩ /
          (Real.sqrt (2 * normalizationScale) : Complex) +
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
            ⟨i + 1, by omega⟩ ⟨j, by omega⟩ /
          (Real.sqrt (2 * normalizationScale) : Complex)) / 2) *
        ((gridScale : Complex) / 2 * (1 - Complex.I)) := by
  apply complexDisplacementIntegral_eq_average_mul
  intro t ht
  have hpoint :
      isingReflectedCenteredRadialGridPosition gridScale n i j +
          (t : Complex) * ((gridScale : Complex) / 2 * (1 - Complex.I)) =
        isingReflectedCenteredRadialGridCellPoint
          gridScale n i j t 0 := by
    rw [isingReflectedCenteredRadialGridCellPoint_eq]
    simp
  rw [hpoint]
  rw [show isingReflectedCenteredRadialGridCellPoint
      gridScale n i j t 0 =
        (starRingEnd Complex)
          (isingCenteredRadialGridCellPoint gridScale n i j t 0) by rfl]
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_cellPoint
    n i j hn gridScale normalizationScale hgridScale hi hj
    t 0 ht.1 ht.2 (le_refl 0) zero_le_one]
  simp [complexBilinearCell]


theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral
    (n i j : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n) :
    complexDisplacementIntegral
        (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
          n hn gridScale normalizationScale)
        (isingReflectedCenteredRadialGridPosition gridScale n i j)
        ((gridScale : Complex) / 2 * (1 + Complex.I)) =
      ((fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
            ⟨i, by omega⟩ ⟨j, by omega⟩ /
          (Real.sqrt (2 * normalizationScale) : Complex) +
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
            ⟨i, by omega⟩ ⟨j + 1, by omega⟩ /
          (Real.sqrt (2 * normalizationScale) : Complex)) / 2) *
        ((gridScale : Complex) / 2 * (1 + Complex.I)) := by
  apply complexDisplacementIntegral_eq_average_mul
  intro t ht
  have hpoint :
      isingReflectedCenteredRadialGridPosition gridScale n i j +
          (t : Complex) * ((gridScale : Complex) / 2 * (1 + Complex.I)) =
        isingReflectedCenteredRadialGridCellPoint
          gridScale n i j 0 t := by
    rw [isingReflectedCenteredRadialGridCellPoint_eq]
    simp
  rw [hpoint]
  rw [show isingReflectedCenteredRadialGridCellPoint
      gridScale n i j 0 t =
        (starRingEnd Complex)
          (isingCenteredRadialGridCellPoint gridScale n i j 0 t) by rfl]
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_cellPoint
    n i j hn gridScale normalizationScale hgridScale hi hj
    0 t (le_refl 0) zero_le_one ht.1 ht.2]
  simp [complexBilinearCell]


theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral_eq_edge
    (n i j : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n) :
    complexDisplacementIntegral
        (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
          n hn gridScale normalizationScale)
        (isingReflectedCenteredRadialGridPosition gridScale n i j)
        ((gridScale : Complex) / 2 * (1 - Complex.I)) =
      reflectedRadialHorizontalEdgeIntegral gridScale
        (fun a b =>
          fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
              n hn a b /
            (Real.sqrt (2 * normalizationScale) : Complex)) i j := by
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral
    n i j hn gridScale normalizationScale hgridScale hi hj]
  unfold reflectedRadialHorizontalEdgeIntegral
  dsimp only
  rw [fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_apply
      n hn i j (by omega) (by omega),
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_apply
      n hn (i + 1) j hi (by omega)]
  ring


theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral_eq_edge
    (n i j : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n) :
    complexDisplacementIntegral
        (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
          n hn gridScale normalizationScale)
        (isingReflectedCenteredRadialGridPosition gridScale n i j)
        ((gridScale : Complex) / 2 * (1 + Complex.I)) =
      reflectedRadialVerticalEdgeIntegral gridScale
        (fun a b =>
          fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
              n hn a b /
            (Real.sqrt (2 * normalizationScale) : Complex)) i j := by
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral
    n i j hn gridScale normalizationScale hgridScale hi hj]
  unfold reflectedRadialVerticalEdgeIntegral
  dsimp only
  rw [fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_apply
      n hn i j (by omega) (by omega),
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_apply
      n hn i (j + 1) (by omega) hj]
  ring


theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negIEdgeIntegral_eq_edge
    (n i j : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n) :
    complexDisplacementIntegral
        (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
          n hn gridScale normalizationScale)
        (isingReflectedCenteredRadialGridPosition gridScale n (i + 1) j)
        (-((gridScale : Complex) / 2 * (1 - Complex.I))) =
      -reflectedRadialHorizontalEdgeIntegral gridScale
        (fun a b =>
          fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
              n hn a b /
            (Real.sqrt (2 * normalizationScale) : Complex)) i j := by
  rw [isingReflectedCenteredRadialGridPosition_succ_i,
    complexDisplacementIntegral_reverse]
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral_eq_edge
    n i j hn gridScale normalizationScale hgridScale hi hj]


theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negJEdgeIntegral_eq_edge
    (n i j : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n) :
    complexDisplacementIntegral
        (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
          n hn gridScale normalizationScale)
        (isingReflectedCenteredRadialGridPosition gridScale n i (j + 1))
        (-((gridScale : Complex) / 2 * (1 + Complex.I))) =
      -reflectedRadialVerticalEdgeIntegral gridScale
        (fun a b =>
          fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
              n hn a b /
            (Real.sqrt (2 * normalizationScale) : Complex)) i j := by
  rw [isingReflectedCenteredRadialGridPosition_succ_j,
    complexDisplacementIntegral_reverse]
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral_eq_edge
    n i j hn gridScale normalizationScale hgridScale hi hj]


theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedAxisStaircasePathIntegral_eq_boundary
    (n i0 j0 width height : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i0 + width + height + 1 < 2 * n)
    (hj : j0 + width + height + 1 < 2 * n) :
    reflectedRadialAxisStaircasePathIntegral
        (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
          n hn gridScale normalizationScale)
        gridScale n i0 j0 width height =
      reflectedRadialAxisStaircaseBoundaryIntegral gridScale
        (fun i j =>
          fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
              n hn i j /
            (Real.sqrt (2 * normalizationScale) : Complex))
        i0 j0 width height := by
  let f :=
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
      n hn gridScale normalizationScale
  let F : Nat -> Nat -> Complex := fun i j =>
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn i j /
      (Real.sqrt (2 * normalizationScale) : Complex)
  let u : Complex := (gridScale : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (gridScale : Complex) / 2 * (1 + Complex.I)
  have hbottom :
      (∑ k ∈ Finset.range width,
        (complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition
              gridScale n (i0 + height + k) (j0 + k)) u +
          complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition
              gridScale n (i0 + height + k + 1) (j0 + k)) v)) =
      ∑ k ∈ Finset.range width,
        (reflectedRadialHorizontalEdgeIntegral gridScale F
            (i0 + height + k) (j0 + k) +
          reflectedRadialVerticalEdgeIntegral gridScale F
            (i0 + height + k + 1) (j0 + k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    dsimp only [f, F, u, v]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral_eq_edge
      n (i0 + height + k) (j0 + k) hn gridScale normalizationScale
      hgridScale (by omega) (by omega)]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral_eq_edge
      n (i0 + height + k + 1) (j0 + k) hn gridScale normalizationScale
      hgridScale (by omega) (by omega)]
  have hright :
      (∑ k ∈ Finset.range height,
        (complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + width + (height - 1 - k) + 1) (j0 + width + k)) v +
          complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + width + (height - 1 - k) + 1)
              (j0 + width + k + 1)) (-u))) =
      ∑ k ∈ Finset.range height,
        (reflectedRadialVerticalEdgeIntegral gridScale F
            (i0 + width + (height - 1 - k) + 1) (j0 + width + k) -
          reflectedRadialHorizontalEdgeIntegral gridScale F
            (i0 + width + (height - 1 - k)) (j0 + width + k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    dsimp only [f, F, u, v]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral_eq_edge
      n (i0 + width + (height - 1 - k) + 1) (j0 + width + k)
      hn gridScale normalizationScale hgridScale (by omega) (by omega)]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negIEdgeIntegral_eq_edge
      n (i0 + width + (height - 1 - k)) (j0 + width + k + 1)
      hn gridScale normalizationScale hgridScale (by omega) (by omega)]
    ring
  have htop :
      (∑ k ∈ Finset.range width,
        (complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + (width - 1 - k) + 1)
              (j0 + height + (width - 1 - k) + 1)) (-u) +
          complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + (width - 1 - k))
              (j0 + height + (width - 1 - k) + 1)) (-v))) =
      ∑ k ∈ Finset.range width,
        (-reflectedRadialHorizontalEdgeIntegral gridScale F
            (i0 + (width - 1 - k))
            (j0 + height + (width - 1 - k) + 1) -
          reflectedRadialVerticalEdgeIntegral gridScale F
            (i0 + (width - 1 - k))
            (j0 + height + (width - 1 - k))) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    dsimp only [f, F, u, v]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negIEdgeIntegral_eq_edge
      n (i0 + (width - 1 - k))
      (j0 + height + (width - 1 - k) + 1)
      hn gridScale normalizationScale hgridScale (by omega) (by omega)]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negJEdgeIntegral_eq_edge
      n (i0 + (width - 1 - k))
      (j0 + height + (width - 1 - k))
      hn gridScale normalizationScale hgridScale (by omega) (by omega)]
    ring
  have hleft :
      (∑ k ∈ Finset.range height,
        (complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + k) (j0 + (height - 1 - k) + 1)) (-v) +
          complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + k) (j0 + (height - 1 - k))) u)) =
      ∑ k ∈ Finset.range height,
        (-reflectedRadialVerticalEdgeIntegral gridScale F
            (i0 + k) (j0 + (height - 1 - k)) +
          reflectedRadialHorizontalEdgeIntegral gridScale F
            (i0 + k) (j0 + (height - 1 - k))) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    dsimp only [f, F, u, v]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negJEdgeIntegral_eq_edge
      n (i0 + k) (j0 + (height - 1 - k))
      hn gridScale normalizationScale hgridScale (by omega) (by omega)]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral_eq_edge
      n (i0 + k) (j0 + (height - 1 - k))
      hn gridScale normalizationScale hgridScale (by omega) (by omega)]
  unfold reflectedRadialAxisStaircasePathIntegral
    reflectedRadialAxisStaircaseBoundaryIntegral
  dsimp only
  change
    (∑ k ∈ Finset.range width,
      (complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition
            gridScale n (i0 + height + k) (j0 + k)) u +
        complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition
            gridScale n (i0 + height + k + 1) (j0 + k)) v)) +
      (∑ k ∈ Finset.range height,
        (complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + width + (height - 1 - k) + 1) (j0 + width + k)) v +
          complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + width + (height - 1 - k) + 1)
              (j0 + width + k + 1)) (-u))) +
      (∑ k ∈ Finset.range width,
        (complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + (width - 1 - k) + 1)
              (j0 + height + (width - 1 - k) + 1)) (-u) +
          complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + (width - 1 - k))
              (j0 + height + (width - 1 - k) + 1)) (-v))) +
      (∑ k ∈ Finset.range height,
        (complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + k) (j0 + (height - 1 - k) + 1)) (-v) +
          complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + k) (j0 + (height - 1 - k))) u)) = _
  rw [hbottom, hright, htop, hleft]


theorem
    fkIsingExpandingBoundarySquareCenteredReflectedRegionContour_eq_zero
    (k : Nat) (cells : Finset (Nat × Nat))
    (hinterior : forall p, p ∈ cells ->
      p.1 + 2 < 2 * fkIsingExpandingSquareSide k ∧
      p.2 + 2 < 2 * fkIsingExpandingSquareSide k) :
    reflectedRadialCellRegionBoundaryIntegral
      (fkIsingExpandingSquareScale k)
      (fun i j =>
        fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k) i j /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex))
      cells = 0 := by
  exact
    fkIsingSquareBoundaryCenteredRadialPatchNormalizedExtension_reflectedRegionContour_eq_zero
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareMesh k)
      cells hinterior


theorem
    fkIsingExpandingBoundarySquareCenteredReflectedAxisStaircaseContour_eq_zero
    (k i0 j0 width height : Nat)
    (hi : i0 + width + height + 1 <
      2 * fkIsingExpandingSquareSide k)
    (hj : j0 + width + height + 1 <
      2 * fkIsingExpandingSquareSide k) :
    reflectedRadialAxisStaircaseBoundaryIntegral
      (fkIsingExpandingSquareScale k)
      (fun i j =>
        fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k) i j /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex))
      i0 j0 width height = 0 := by
  apply reflectedRadialAxisStaircaseBoundaryIntegral_eq_zero_of_cellCR
  intro a b ha hb
  apply IsingCellCRAt.div_const
  apply fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
  · omega
  · omega


theorem
    fkIsingExpandingBoundarySquareCenteredReflectedAxisStaircasePathIntegral_eq_zero
    (k i0 j0 width height : Nat)
    (hi : i0 + width + height + 1 <
      2 * fkIsingExpandingSquareSide k)
    (hj : j0 + width + height + 1 <
      2 * fkIsingExpandingSquareSide k) :
    reflectedRadialAxisStaircasePathIntegral
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k)
      i0 j0 width height = 0 := by
  unfold fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedAxisStaircasePathIntegral_eq_boundary
    (fkIsingExpandingSquareSide k) i0 j0 width height
    (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareMesh k)
    (fkIsingExpandingSquareScale_pos k).ne' hi hj]
  exact
    fkIsingExpandingBoundarySquareCenteredReflectedAxisStaircaseContour_eq_zero
      k i0 j0 width height hi hj


theorem
    fkIsingExpandingBoundarySquare_eventually_axisSnapStaircasePathIntegral_eq_zero
    (z w : Complex) (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    ∀ᶠ k in atTop,
      reflectedRadialAxisStaircasePathIntegral
          (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k)
          (fkIsingExpandingSquareScale k)
          (fkIsingExpandingSquareSide k)
          (reflectedRadialAxisSnapBaseI
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareScale k) z w)
          (reflectedRadialAxisSnapBaseJ
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareScale k) z)
          (reflectedRadialAxisSnapWidth
            (fkIsingExpandingSquareScale k) z w)
          (reflectedRadialAxisSnapHeight
            (fkIsingExpandingSquareScale k) z w) = 0 := by
  filter_upwards
    [fkIsingExpandingSquare_eventually_axisSnap_interior z w hre him]
      with k hk
  exact
    fkIsingExpandingBoundarySquareCenteredReflectedAxisStaircasePathIntegral_eq_zero
      k
      (reflectedRadialAxisSnapBaseI
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareScale k) z w)
      (reflectedRadialAxisSnapBaseJ
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareScale k) z)
      (reflectedRadialAxisSnapWidth
        (fkIsingExpandingSquareScale k) z w)
      (reflectedRadialAxisSnapHeight
        (fkIsingExpandingSquareScale k) z w)
      hk.2.2.1 hk.2.2.2


theorem fkIsingExpandingBoundarySquareCenteredReflectedCellPathIntegral_eq_zero
    (k i j : Nat)
    (hi : i + 2 < 2 * fkIsingExpandingSquareSide k)
    (hj : j + 2 < 2 * fkIsingExpandingSquareSide k) :
    reflectedRadialBilinearCellPathIntegral
      (fkIsingExpandingSquareScale k)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          (fkIsingExpandingSquareSide k)
          (fkIsingExpandingSquareSide_pos k) i j /
        (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex))
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          (fkIsingExpandingSquareSide k)
          (fkIsingExpandingSquareSide_pos k) (i + 1) j /
        (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex))
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          (fkIsingExpandingSquareSide k)
          (fkIsingExpandingSquareSide_pos k) i (j + 1) /
        (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex))
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          (fkIsingExpandingSquareSide k)
          (fkIsingExpandingSquareSide_pos k) (i + 1) (j + 1) /
        (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) = 0 := by
  exact
    fkIsingSquareBoundaryCenteredRadialPatch_reflectedCellPathIntegral_eq_zero
      (fkIsingExpandingSquareSide k) i j
      (fkIsingExpandingSquareSide_pos k) hi hj
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareMesh k)

theorem reflectedRadialBilinearCellContour_eq_zero_of_IsingCellCRAt
    (mesh : Real) (F : Nat -> Nat -> Complex) (i j : Nat)
    (hCR : IsingCellCRAt F i j) :
    reflectedRadialBilinearCellContour mesh
      (F i j) (F (i + 1) j) (F i (j + 1)) (F (i + 1) (j + 1)) = 0 := by
  exact reflectedRadialBilinearCellContour_eq_zero_of_cellCR mesh _ _ _ _ hCR

end
end StatMech.Universality
