/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

theorem boundaryVertexLocalizedSimonCurrentRatio_eq_boxSimonCurrentRatio
    (β H : ℝ) (n : ℕ) {v : FK.boxVerts 3 n}
    (hv : FK.boxBoundary 3 n v) :
    boundaryVertexLocalizedSimonCurrentRatio β H n v =
      boundaryVertexBoxSimonCurrentRatio β n v := by
  simpa [
    boundaryVertexLocalizedSimonCurrentRatio,
    boundaryVertexBoxSimonCurrentRatio] using
    finiteBoundaryGhostLocalizedExpectation_boundary_eq_boxExpectation
      β H n hv


theorem boundaryVertexBoxSimonCurrentRatio_nonneg
    {β : ℝ} {n : ℕ} (v : FK.boxVerts 3 n)
    (hβ : 0 ≤ β) :
    0 ≤ boundaryVertexBoxSimonCurrentRatio β n v := by
  simpa [boundaryVertexBoxSimonCurrentRatio] using
    Sharpness.ssl_expectationJ_nonneg (FK.boxGraph 3 n) β (fun _ => 1)
      hβ (fun _ => by norm_num)
      (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v})


theorem boundaryVertexTanhNormalizedEmptyBoundaryTerm_eq_currentTerm
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) :
    boundaryVertexTanhNormalizedEmptyBoundaryTerm β H n v =
      boundaryVertexTanhNormalizedEmptyBoundaryCurrentTerm β H n v := by
  simp [boundaryVertexTanhNormalizedEmptyBoundaryTerm,
    boundaryVertexTanhNormalizedEmptyBoundaryCurrentTerm,
    edgeCopySourcePairEmptyCollapsedSum_eq_currentSum_mul]


theorem boundaryVertexTanhNormalizedSimonDenominator_eq_currentDenominator
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) :
    boundaryVertexTanhNormalizedSimonDenominator β H n v =
      boundaryVertexTanhNormalizedSimonCurrentDenominator β H n v := by
  simp [boundaryVertexTanhNormalizedSimonDenominator,
    boundaryVertexTanhNormalizedSimonCurrentDenominator,
    edgeCopySourcePairEmptyCollapsedSum_eq_currentSum_mul]


theorem boundaryVertexTanhNormalizedOnePointTerm_eq_currentTerm
    (β H : ℝ) (n : ℕ) :
    boundaryVertexTanhNormalizedOnePointTerm β H n =
      boundaryVertexTanhNormalizedOnePointCurrentTerm β H n := by
  simp [boundaryVertexTanhNormalizedOnePointTerm,
    boundaryVertexTanhNormalizedOnePointCurrentTerm,
    edgeCopySourcePairSum_eq_currentSum_mul]


theorem boundaryVertexTanhNormalizedBoundaryPairTerm_eq_currentTerm
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) :
    boundaryVertexTanhNormalizedBoundaryPairTerm β H n v =
      boundaryVertexTanhNormalizedBoundaryPairCurrentTerm β H n v := by
  simp [boundaryVertexTanhNormalizedBoundaryPairTerm,
    boundaryVertexTanhNormalizedBoundaryPairCurrentTerm,
    edgeCopySourcePairSum_eq_currentSum_mul]


theorem tanhNormalizedOnePointCurrentThird_of_ratioThird_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (cap : ℝ)
    (h :
      cap * boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n ≤
        boundaryVertexLocalizedSimonCurrentRatio β H n v / 3) :
    cap * boundaryVertexTanhNormalizedOnePointCurrentTerm β H n ≤
      boundaryVertexTanhNormalizedSimonCurrentDenominator β H n v / 3 := by
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let Z0 := Sharpness.currentSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  let Z1 := Sharpness.currentSum G β J
    (finiteBoundaryGhostOnePointSource 3 n)
  let E := Sharpness.expectationJ G β
    (Sharpness.couplingIn J (finiteBoundaryGhostOriginalSet 3 n))
    ({some (IsingFK.boxOrigin 3 n), some v} :
      Finset (Option (FK.boxVerts 3 n)))
  let R := ((β * H) * (β * H)) / Real.tanh (β * H)
  have hZ0pos : 0 < Z0 := by
    simpa [G, J, Z0] using currentSum_empty_pos G β J
  have hZ0nonneg : 0 ≤ Z0 * Z0 :=
    mul_nonneg (le_of_lt hZ0pos) (le_of_lt hZ0pos)
  have hscaled := mul_le_mul_of_nonneg_right h hZ0nonneg
  change (cap * (R * (Z1 / Z0))) * (Z0 * Z0) ≤
    (E / 3) * (Z0 * Z0) at hscaled
  have hleft :
      (cap * (R * (Z1 / Z0))) * (Z0 * Z0) =
        cap * (R * (Z1 * Z0)) := by
    field_simp [ne_of_gt hZ0pos]
  have hright : (E / 3) * (Z0 * Z0) = E * (Z0 * Z0) / 3 := by
    ring
  change cap * (R * (Z1 * Z0)) ≤ E * (Z0 * Z0) / 3
  rwa [hleft, hright] at hscaled


theorem tanhNormalizedBoundaryPairCurrentThird_of_ratioThird_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (cap : ℝ)
    (h :
      cap * boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v ≤
        boundaryVertexLocalizedSimonCurrentRatio β H n v / 3) :
    cap * boundaryVertexTanhNormalizedBoundaryPairCurrentTerm β H n v ≤
      boundaryVertexTanhNormalizedSimonCurrentDenominator β H n v / 3 := by
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let A : Finset (Option (FK.boxVerts 3 n)) :=
    ({some (IsingFK.boxOrigin 3 n)} :
      Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
  let B : Finset (Option (FK.boxVerts 3 n)) :=
    ({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}
  let Z0 := Sharpness.currentSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  let ZA := Sharpness.currentSum G β J A
  let ZB := Sharpness.currentSum G β J B
  let E := Sharpness.expectationJ G β
    (Sharpness.couplingIn J (finiteBoundaryGhostOriginalSet 3 n))
    ({some (IsingFK.boxOrigin 3 n), some v} :
      Finset (Option (FK.boxVerts 3 n)))
  let R := ((β * H) * (β * H)) / Real.tanh (β * H)
  have hZ0pos : 0 < Z0 := by
    simpa [G, J, Z0] using currentSum_empty_pos G β J
  have hZ0sqpos : 0 < Z0 * Z0 := mul_pos hZ0pos hZ0pos
  have hscaled :=
    mul_le_mul_of_nonneg_right h (le_of_lt hZ0sqpos)
  change (cap * (R * ((ZA * ZB) / (Z0 * Z0)))) * (Z0 * Z0) ≤
    (E / 3) * (Z0 * Z0) at hscaled
  have hleft :
      (cap * (R * ((ZA * ZB) / (Z0 * Z0)))) * (Z0 * Z0) =
        cap * (R * (ZA * ZB)) := by
    field_simp [ne_of_gt hZ0sqpos]
  have hright : (E / 3) * (Z0 * Z0) = E * (Z0 * Z0) / 3 := by
    ring
  change cap * (R * (ZA * ZB)) ≤ E * (Z0 * Z0) / 3
  rwa [hleft, hright] at hscaled


theorem tanhNormalizedOnePointCurrentShare_of_ratioShare_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (cap share : ℝ)
    (h :
      cap * boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n ≤
        share * boundaryVertexLocalizedSimonCurrentRatio β H n v) :
    cap * boundaryVertexTanhNormalizedOnePointCurrentTerm β H n ≤
      share * boundaryVertexTanhNormalizedSimonCurrentDenominator β H n v := by
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let Z0 := Sharpness.currentSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  let Z1 := Sharpness.currentSum G β J
    (finiteBoundaryGhostOnePointSource 3 n)
  let E := Sharpness.expectationJ G β
    (Sharpness.couplingIn J (finiteBoundaryGhostOriginalSet 3 n))
    ({some (IsingFK.boxOrigin 3 n), some v} :
      Finset (Option (FK.boxVerts 3 n)))
  let R := ((β * H) * (β * H)) / Real.tanh (β * H)
  have hZ0pos : 0 < Z0 := by
    simpa [G, J, Z0] using currentSum_empty_pos G β J
  have hZ0nonneg : 0 ≤ Z0 * Z0 :=
    mul_nonneg (le_of_lt hZ0pos) (le_of_lt hZ0pos)
  have hscaled := mul_le_mul_of_nonneg_right h hZ0nonneg
  change (cap * (R * (Z1 / Z0))) * (Z0 * Z0) ≤
    (share * E) * (Z0 * Z0) at hscaled
  have hleft :
      (cap * (R * (Z1 / Z0))) * (Z0 * Z0) =
        cap * (R * (Z1 * Z0)) := by
    field_simp [ne_of_gt hZ0pos]
  have hright :
      (share * E) * (Z0 * Z0) = share * (E * (Z0 * Z0)) := by
    ring
  change cap * (R * (Z1 * Z0)) ≤ share * (E * (Z0 * Z0))
  rwa [hleft, hright] at hscaled


theorem tanhNormalizedBoundaryPairCurrentShare_of_ratioShare_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (cap share : ℝ)
    (h :
      cap * boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
          β H n v ≤
        share * boundaryVertexLocalizedSimonCurrentRatio β H n v) :
    cap * boundaryVertexTanhNormalizedBoundaryPairCurrentTerm β H n v ≤
      share * boundaryVertexTanhNormalizedSimonCurrentDenominator
        β H n v := by
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let A : Finset (Option (FK.boxVerts 3 n)) :=
    ({some (IsingFK.boxOrigin 3 n)} :
      Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
  let B : Finset (Option (FK.boxVerts 3 n)) :=
    ({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}
  let Z0 := Sharpness.currentSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  let ZA := Sharpness.currentSum G β J A
  let ZB := Sharpness.currentSum G β J B
  let E := Sharpness.expectationJ G β
    (Sharpness.couplingIn J (finiteBoundaryGhostOriginalSet 3 n))
    ({some (IsingFK.boxOrigin 3 n), some v} :
      Finset (Option (FK.boxVerts 3 n)))
  let R := ((β * H) * (β * H)) / Real.tanh (β * H)
  have hZ0pos : 0 < Z0 := by
    simpa [G, J, Z0] using currentSum_empty_pos G β J
  have hZ0sqpos : 0 < Z0 * Z0 := mul_pos hZ0pos hZ0pos
  have hscaled :=
    mul_le_mul_of_nonneg_right h (le_of_lt hZ0sqpos)
  change (cap * (R * ((ZA * ZB) / (Z0 * Z0)))) * (Z0 * Z0) ≤
    (share * E) * (Z0 * Z0) at hscaled
  have hleft :
      (cap * (R * ((ZA * ZB) / (Z0 * Z0)))) * (Z0 * Z0) =
        cap * (R * (ZA * ZB)) := by
    field_simp [ne_of_gt hZ0sqpos]
  have hright :
      (share * E) * (Z0 * Z0) = share * (E * (Z0 * Z0)) := by
    ring
  change cap * (R * (ZA * ZB)) ≤ share * (E * (Z0 * Z0))
  rwa [hleft, hright] at hscaled


theorem tanhNormalizedEmptyBoundaryCurrentShare_of_ratioShare_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (share : ℝ)
    (h :
      boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v ≤
        share * boundaryVertexLocalizedSimonCurrentRatio β H n v) :
    boundaryVertexTanhNormalizedEmptyBoundaryCurrentTerm β H n v ≤
      share * boundaryVertexTanhNormalizedSimonCurrentDenominator β H n v := by
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let A : Finset (Option (FK.boxVerts 3 n)) :=
    ({some (IsingFK.boxOrigin 3 n)} :
      Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
  let Z0 := Sharpness.currentSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  let ZA := Sharpness.currentSum G β J A
  let E := Sharpness.expectationJ G β
    (Sharpness.couplingIn J (finiteBoundaryGhostOriginalSet 3 n))
    ({some (IsingFK.boxOrigin 3 n), some v} :
      Finset (Option (FK.boxVerts 3 n)))
  let R := (β * H) / Real.tanh (β * H)
  have hZ0pos : 0 < Z0 := by
    simpa [G, J, Z0] using currentSum_empty_pos G β J
  have hZ0nonneg : 0 ≤ Z0 * Z0 :=
    mul_nonneg (le_of_lt hZ0pos) (le_of_lt hZ0pos)
  have hscaled := mul_le_mul_of_nonneg_right h hZ0nonneg
  change (R * (ZA / Z0)) * (Z0 * Z0) ≤
    (share * E) * (Z0 * Z0) at hscaled
  have hleft : (R * (ZA / Z0)) * (Z0 * Z0) = R * (ZA * Z0) := by
    field_simp [ne_of_gt hZ0pos]
  have hright :
      (share * E) * (Z0 * Z0) = share * (E * (Z0 * Z0)) := by
    ring
  change R * (ZA * Z0) ≤ share * (E * (Z0 * Z0))
  rwa [hleft, hright] at hscaled


theorem boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 < β) (hH : 0 < H) :
    0 ≤ boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let T := Real.tanh (β * H)
  let C := (β * H) * (β * H)
  let Z0 := Sharpness.currentSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  let Z1 := Sharpness.currentSum G β J
    (finiteBoundaryGhostOnePointSource 3 n)
  have hβnonneg : 0 ≤ β := le_of_lt hβ
  have hHnonneg : 0 ≤ H := le_of_lt hH
  have hJ : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hHnonneg
      (fun _ => by norm_num)
  have hTnonneg : 0 ≤ T :=
    le_of_lt (real_tanh_pos_of_pos (mul_pos hβ hH))
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hβnonneg hHnonneg)
      (mul_nonneg hβnonneg hHnonneg)
  have hcoef : 0 ≤ C / T := div_nonneg hC hTnonneg
  have hZ1 : 0 ≤ Z1 := by
    simpa [G, J, Z1] using
      Sharpness.ssl_currentSum_nonneg G β J hβnonneg hJ
        (finiteBoundaryGhostOnePointSource 3 n)
  have hZ0pos : 0 < Z0 := by
    simpa [G, J, Z0] using currentSum_empty_pos G β J
  have hratio : 0 ≤ Z1 / Z0 := div_nonneg hZ1 (le_of_lt hZ0pos)
  simpa [
    boundaryVertexTanhNormalizedOnePointCurrentRatioTerm,
    G, J, T, C, Z0, Z1] using
    mul_nonneg hcoef hratio


theorem boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
    {β H : ℝ} {n : ℕ} (v : FK.boxVerts 3 n)
    (hβ : 0 < β) (hH : 0 < H) :
    0 ≤
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let T := Real.tanh (β * H)
  let C := (β * H) * (β * H)
  let A : Finset (Option (FK.boxVerts 3 n)) :=
    ({some (IsingFK.boxOrigin 3 n)} :
      Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
  let B : Finset (Option (FK.boxVerts 3 n)) :=
    ({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}
  let Z0 := Sharpness.currentSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  let ZA := Sharpness.currentSum G β J A
  let ZB := Sharpness.currentSum G β J B
  have hβnonneg : 0 ≤ β := le_of_lt hβ
  have hHnonneg : 0 ≤ H := le_of_lt hH
  have hJ : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hHnonneg
      (fun _ => by norm_num)
  have hTnonneg : 0 ≤ T :=
    le_of_lt (real_tanh_pos_of_pos (mul_pos hβ hH))
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hβnonneg hHnonneg)
      (mul_nonneg hβnonneg hHnonneg)
  have hcoef : 0 ≤ C / T := div_nonneg hC hTnonneg
  have hZA : 0 ≤ ZA := by
    simpa [G, J, A, ZA] using
      Sharpness.ssl_currentSum_nonneg G β J hβnonneg hJ A
  have hZB : 0 ≤ ZB := by
    simpa [G, J, B, ZB] using
      Sharpness.ssl_currentSum_nonneg G β J hβnonneg hJ B
  have hZ0pos : 0 < Z0 := by
    simpa [G, J, Z0] using currentSum_empty_pos G β J
  have hden : 0 ≤ Z0 * Z0 :=
    mul_nonneg (le_of_lt hZ0pos) (le_of_lt hZ0pos)
  have hratio : 0 ≤ (ZA * ZB) / (Z0 * Z0) :=
    div_nonneg (mul_nonneg hZA hZB) hden
  simpa [
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm,
    G, J, T, C, A, B, Z0, ZA, ZB] using
    mul_nonneg hcoef hratio


theorem boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm_nonneg
    {β H : ℝ} {n : ℕ} (v : FK.boxVerts 3 n)
    (hβ : 0 < β) (hH : 0 < H) :
    0 ≤
      boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let T := Real.tanh (β * H)
  let A : Finset (Option (FK.boxVerts 3 n)) :=
    ({some (IsingFK.boxOrigin 3 n)} :
      Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
  let Z0 := Sharpness.currentSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  let ZA := Sharpness.currentSum G β J A
  have hβnonneg : 0 ≤ β := le_of_lt hβ
  have hHnonneg : 0 ≤ H := le_of_lt hH
  have hJ : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hHnonneg
      (fun _ => by norm_num)
  have hTnonneg : 0 ≤ T :=
    le_of_lt (real_tanh_pos_of_pos (mul_pos hβ hH))
  have hcoef : 0 ≤ (β * H) / T :=
    div_nonneg (mul_nonneg hβnonneg hHnonneg) hTnonneg
  have hZA : 0 ≤ ZA := by
    simpa [G, J, A, ZA] using
      Sharpness.ssl_currentSum_nonneg G β J hβnonneg hJ A
  have hZ0pos : 0 < Z0 := by
    simpa [G, J, Z0] using currentSum_empty_pos G β J
  have hratio : 0 ≤ ZA / Z0 := div_nonneg hZA (le_of_lt hZ0pos)
  simpa [
    boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm,
    G, J, T, A, Z0, ZA] using
    mul_nonneg hcoef hratio


theorem tanhNormalizedEmptyBoundaryCurrentThird_of_ratioThird_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (h :
      boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v ≤
        boundaryVertexLocalizedSimonCurrentRatio β H n v / 3) :
    boundaryVertexTanhNormalizedEmptyBoundaryCurrentTerm β H n v ≤
      boundaryVertexTanhNormalizedSimonCurrentDenominator β H n v / 3 := by
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let A : Finset (Option (FK.boxVerts 3 n)) :=
    ({some (IsingFK.boxOrigin 3 n)} :
      Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
  let Z0 := Sharpness.currentSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  let ZA := Sharpness.currentSum G β J A
  let E := Sharpness.expectationJ G β
    (Sharpness.couplingIn J (finiteBoundaryGhostOriginalSet 3 n))
    ({some (IsingFK.boxOrigin 3 n), some v} :
      Finset (Option (FK.boxVerts 3 n)))
  let R := (β * H) / Real.tanh (β * H)
  have hZ0pos : 0 < Z0 := by
    simpa [G, J, Z0] using currentSum_empty_pos G β J
  have hZ0nonneg : 0 ≤ Z0 * Z0 :=
    mul_nonneg (le_of_lt hZ0pos) (le_of_lt hZ0pos)
  have hscaled := mul_le_mul_of_nonneg_right h hZ0nonneg
  change (R * (ZA / Z0)) * (Z0 * Z0) ≤ (E / 3) * (Z0 * Z0) at hscaled
  have hleft : (R * (ZA / Z0)) * (Z0 * Z0) = R * (ZA * Z0) := by
    field_simp [ne_of_gt hZ0pos]
  have hright : (E / 3) * (Z0 * Z0) = E * (Z0 * Z0) / 3 := by
    ring
  change R * (ZA * Z0) ≤ E * (Z0 * Z0) / 3
  rwa [hleft, hright] at hscaled


theorem finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm_eq_tanh_mul_normalized
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hT : Real.tanh (β * H) ≠ 0) :
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v =
      Real.tanh (β * H) *
        boundaryVertexTanhNormalizedEmptyBoundaryTerm β H n v := by
  unfold finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
    boundaryVertexTanhNormalizedEmptyBoundaryTerm
  let T := Real.tanh (β * H)
  let A : Finset (Option (FK.boxVerts 3 n)) :=
    ({some (IsingFK.boxOrigin 3 n)} :
      Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
  let E :=
    edgeCopySourcePairEmptyCollapsedSum
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) A
  have hT' : T ≠ 0 := by
    simpa [T] using hT
  change (β * H) * E = T * (((β * H) / T) * E)
  field_simp [hT']


theorem finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_eq_tanh_mul_normalized
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : FK.boxBoundary 3 n v) :
    finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v =
      Real.tanh (β * H) *
        boundaryVertexTanhNormalizedSimonDenominator β H n v := by
  unfold finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
    boundaryVertexTanhNormalizedSimonDenominator
  rw [finiteBoundaryGhostSimonWeight_some_none_of_boundary β H n hv]
  ring


theorem finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_eq_tanh_mul_normalized
    {β H : ℝ} {n : ℕ}
    (hT : Real.tanh (β * H) ≠ 0) :
    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n =
      Real.tanh (β * H) *
        boundaryVertexTanhNormalizedOnePointTerm β H n := by
  unfold finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
    boundaryVertexTanhNormalizedOnePointTerm
  let T := Real.tanh (β * H)
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let C := (β * H) * (β * H)
  let E := edgeCopySourcePairSum G β J
    (finiteBoundaryGhostOnePointSource 3 n)
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  have hT' : T ≠ 0 := by
    simpa [T] using hT
  change C * E = T * ((C / T) * E)
  field_simp [hT']


theorem finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_eq_tanh_mul_normalized
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hT : Real.tanh (β * H) ≠ 0) :
    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm β H n v =
      Real.tanh (β * H) *
        boundaryVertexTanhNormalizedBoundaryPairTerm β H n v := by
  unfold finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
    boundaryVertexTanhNormalizedBoundaryPairTerm
  let T := Real.tanh (β * H)
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let C := (β * H) * (β * H)
  let A : Finset (Option (FK.boxVerts 3 n)) :=
    ({some (IsingFK.boxOrigin 3 n)} :
      Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
  let B : Finset (Option (FK.boxVerts 3 n)) :=
    ({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}
  let E := edgeCopySourcePairSum G β J A B
  have hT' : T ≠ 0 := by
    simpa [T] using hT
  change C * E = T * ((C / T) * E)
  field_simp [hT']


theorem onePointThird_of_tanhNormalizedOnePointThird_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 < β) (hH : 0 < H)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (cap : ℝ)
    (h :
      cap * boundaryVertexTanhNormalizedOnePointTerm β H n ≤
        boundaryVertexTanhNormalizedSimonDenominator β H n v / 3) :
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
        β H n ≤
      finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v / 3 := by
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  have hTpos : 0 < Real.tanh (β * H) :=
    real_tanh_pos_of_pos (mul_pos hβ hH)
  have hTne : Real.tanh (β * H) ≠ 0 := ne_of_gt hTpos
  calc
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
        β H n =
        Real.tanh (β * H) *
          (cap * boundaryVertexTanhNormalizedOnePointTerm β H n) := by
      rw [
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_eq_tanh_mul_normalized
          hTne]
      ring
    _ ≤
        Real.tanh (β * H) *
          (boundaryVertexTanhNormalizedSimonDenominator β H n v / 3) :=
      mul_le_mul_of_nonneg_left h (le_of_lt hTpos)
    _ =
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v / 3 := by
      rw [
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_eq_tanh_mul_normalized
          hvbdry]
      ring


theorem boundaryPairThird_of_tanhNormalizedBoundaryPairThird_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 < β) (hH : 0 < H)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (cap : ℝ)
    (h :
      cap * boundaryVertexTanhNormalizedBoundaryPairTerm β H n v ≤
        boundaryVertexTanhNormalizedSimonDenominator β H n v / 3) :
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
        β H n v ≤
      finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v / 3 := by
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  have hTpos : 0 < Real.tanh (β * H) :=
    real_tanh_pos_of_pos (mul_pos hβ hH)
  have hTne : Real.tanh (β * H) ≠ 0 := ne_of_gt hTpos
  calc
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
        β H n v =
        Real.tanh (β * H) *
          (cap * boundaryVertexTanhNormalizedBoundaryPairTerm β H n v) := by
      rw [
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_eq_tanh_mul_normalized
          hTne]
      ring
    _ ≤
        Real.tanh (β * H) *
          (boundaryVertexTanhNormalizedSimonDenominator β H n v / 3) :=
      mul_le_mul_of_nonneg_left h (le_of_lt hTpos)
    _ =
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v / 3 := by
      rw [
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_eq_tanh_mul_normalized
          hvbdry]
      ring


theorem emptyBoundaryThird_of_tanhNormalizedEmptyBoundaryThird_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 < β) (hH : 0 < H)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (h :
      boundaryVertexTanhNormalizedEmptyBoundaryTerm β H n v ≤
        boundaryVertexTanhNormalizedSimonDenominator β H n v / 3) :
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v ≤
      finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v / 3 := by
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  have hTpos : 0 < Real.tanh (β * H) :=
    real_tanh_pos_of_pos (mul_pos hβ hH)
  have hTne : Real.tanh (β * H) ≠ 0 := ne_of_gt hTpos
  calc
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v =
        Real.tanh (β * H) *
          boundaryVertexTanhNormalizedEmptyBoundaryTerm β H n v :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm_eq_tanh_mul_normalized
        hTne
    _ ≤
        Real.tanh (β * H) *
          (boundaryVertexTanhNormalizedSimonDenominator β H n v / 3) :=
      mul_le_mul_of_nonneg_left h (le_of_lt hTpos)
    _ =
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v / 3 := by
      rw [
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_eq_tanh_mul_normalized
          hvbdry]
      ring


theorem emptyBoundaryThird_of_tanhNormalizedEmptyBoundaryCurrentRatioThird_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 < β) (hH : 0 < H)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (h :
      boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v ≤
        boundaryVertexLocalizedSimonCurrentRatio β H n v / 3) :
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v ≤
      finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v / 3 := by
  have hcurrent :
      boundaryVertexTanhNormalizedEmptyBoundaryCurrentTerm β H n v ≤
        boundaryVertexTanhNormalizedSimonCurrentDenominator β H n v / 3 :=
    tanhNormalizedEmptyBoundaryCurrentThird_of_ratioThird_pointwise h
  have hnormalized :
      boundaryVertexTanhNormalizedEmptyBoundaryTerm β H n v ≤
        boundaryVertexTanhNormalizedSimonDenominator β H n v / 3 := by
    simpa [
      boundaryVertexTanhNormalizedEmptyBoundaryTerm_eq_currentTerm,
      boundaryVertexTanhNormalizedSimonDenominator_eq_currentDenominator]
      using hcurrent
  exact
    emptyBoundaryThird_of_tanhNormalizedEmptyBoundaryThird_pointwise
      hβ hH hv hnormalized


theorem tanhNormalizedEmptyBoundaryCurrentRatioThird_of_boxRatioThird_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (h :
      boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v ≤
        boundaryVertexBoxSimonCurrentRatio β n v / 3) :
    boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v ≤
      boundaryVertexLocalizedSimonCurrentRatio β H n v / 3 := by
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  simpa [
    boundaryVertexLocalizedSimonCurrentRatio_eq_boxSimonCurrentRatio
      β H n hvbdry] using h


theorem tanhNormalizedOnePointCurrentRatioThird_of_boxRatioThird_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (cap : ℝ)
    (h :
      cap * boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n ≤
        boundaryVertexBoxSimonCurrentRatio β n v / 3) :
    cap * boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n ≤
      boundaryVertexLocalizedSimonCurrentRatio β H n v / 3 := by
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  simpa [
    boundaryVertexLocalizedSimonCurrentRatio_eq_boxSimonCurrentRatio
      β H n hvbdry] using h


theorem tanhNormalizedBoundaryPairCurrentRatioThird_of_boxRatioThird_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (cap : ℝ)
    (h :
      cap * boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
          β H n v ≤
        boundaryVertexBoxSimonCurrentRatio β n v / 3) :
    cap * boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
        β H n v ≤
      boundaryVertexLocalizedSimonCurrentRatio β H n v / 3 := by
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  simpa [
    boundaryVertexLocalizedSimonCurrentRatio_eq_boxSimonCurrentRatio
      β H n hvbdry] using h


theorem onePointShare_of_boxRatioCurrentRatioShare_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 < β) (hH : 0 < H)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (cap share : ℝ)
    (h :
      cap * boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n ≤
        share * boundaryVertexBoxSimonCurrentRatio β n v) :
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
        β H n ≤
      share * finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
        β H n v := by
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  have hTpos : 0 < Real.tanh (β * H) :=
    real_tanh_pos_of_pos (mul_pos hβ hH)
  have hTne : Real.tanh (β * H) ≠ 0 := ne_of_gt hTpos
  have hlocalized :
      cap * boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n ≤
        share * boundaryVertexLocalizedSimonCurrentRatio β H n v := by
    simpa [
      boundaryVertexLocalizedSimonCurrentRatio_eq_boxSimonCurrentRatio
        β H n hvbdry] using h
  have hcurrent :
      cap * boundaryVertexTanhNormalizedOnePointCurrentTerm β H n ≤
        share * boundaryVertexTanhNormalizedSimonCurrentDenominator
          β H n v :=
    tanhNormalizedOnePointCurrentShare_of_ratioShare_pointwise
      cap share hlocalized
  have hnormalized :
      cap * boundaryVertexTanhNormalizedOnePointTerm β H n ≤
        share * boundaryVertexTanhNormalizedSimonDenominator β H n v := by
    simpa [
      boundaryVertexTanhNormalizedOnePointTerm_eq_currentTerm,
      boundaryVertexTanhNormalizedSimonDenominator_eq_currentDenominator]
      using hcurrent
  calc
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
        β H n =
        Real.tanh (β * H) *
          (cap * boundaryVertexTanhNormalizedOnePointTerm β H n) := by
      rw [
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_eq_tanh_mul_normalized
          hTne]
      ring
    _ ≤
        Real.tanh (β * H) *
          (share * boundaryVertexTanhNormalizedSimonDenominator β H n v) :=
      mul_le_mul_of_nonneg_left hnormalized (le_of_lt hTpos)
    _ =
        share * finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
          β H n v := by
      rw [
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_eq_tanh_mul_normalized
          hvbdry]
      ring


theorem boundaryPairShare_of_boxRatioCurrentRatioShare_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 < β) (hH : 0 < H)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (cap share : ℝ)
    (h :
      cap * boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
          β H n v ≤
        share * boundaryVertexBoxSimonCurrentRatio β n v) :
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
        β H n v ≤
      share * finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
        β H n v := by
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  have hTpos : 0 < Real.tanh (β * H) :=
    real_tanh_pos_of_pos (mul_pos hβ hH)
  have hTne : Real.tanh (β * H) ≠ 0 := ne_of_gt hTpos
  have hlocalized :
      cap * boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
          β H n v ≤
        share * boundaryVertexLocalizedSimonCurrentRatio β H n v := by
    simpa [
      boundaryVertexLocalizedSimonCurrentRatio_eq_boxSimonCurrentRatio
        β H n hvbdry] using h
  have hcurrent :
      cap * boundaryVertexTanhNormalizedBoundaryPairCurrentTerm β H n v ≤
        share * boundaryVertexTanhNormalizedSimonCurrentDenominator
          β H n v :=
    tanhNormalizedBoundaryPairCurrentShare_of_ratioShare_pointwise
      cap share hlocalized
  have hnormalized :
      cap * boundaryVertexTanhNormalizedBoundaryPairTerm β H n v ≤
        share * boundaryVertexTanhNormalizedSimonDenominator β H n v := by
    simpa [
      boundaryVertexTanhNormalizedBoundaryPairTerm_eq_currentTerm,
      boundaryVertexTanhNormalizedSimonDenominator_eq_currentDenominator]
      using hcurrent
  calc
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
        β H n v =
        Real.tanh (β * H) *
          (cap * boundaryVertexTanhNormalizedBoundaryPairTerm β H n v) := by
      rw [
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_eq_tanh_mul_normalized
          hTne]
      ring
    _ ≤
        Real.tanh (β * H) *
          (share * boundaryVertexTanhNormalizedSimonDenominator β H n v) :=
      mul_le_mul_of_nonneg_left hnormalized (le_of_lt hTpos)
    _ =
        share * finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
          β H n v := by
      rw [
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_eq_tanh_mul_normalized
          hvbdry]
      ring


theorem emptyBoundaryShare_of_boxRatioCurrentRatioShare_pointwise
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 < β) (hH : 0 < H)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (share : ℝ)
    (h :
      boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v ≤
        share * boundaryVertexBoxSimonCurrentRatio β n v) :
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v ≤
      share * finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
        β H n v := by
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  have hTpos : 0 < Real.tanh (β * H) :=
    real_tanh_pos_of_pos (mul_pos hβ hH)
  have hTne : Real.tanh (β * H) ≠ 0 := ne_of_gt hTpos
  have hlocalized :
      boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v ≤
        share * boundaryVertexLocalizedSimonCurrentRatio β H n v := by
    simpa [
      boundaryVertexLocalizedSimonCurrentRatio_eq_boxSimonCurrentRatio
        β H n hvbdry] using h
  have hcurrent :
      boundaryVertexTanhNormalizedEmptyBoundaryCurrentTerm β H n v ≤
        share * boundaryVertexTanhNormalizedSimonCurrentDenominator
          β H n v :=
    tanhNormalizedEmptyBoundaryCurrentShare_of_ratioShare_pointwise
      share hlocalized
  have hnormalized :
      boundaryVertexTanhNormalizedEmptyBoundaryTerm β H n v ≤
        share * boundaryVertexTanhNormalizedSimonDenominator β H n v := by
    simpa [
      boundaryVertexTanhNormalizedEmptyBoundaryTerm_eq_currentTerm,
      boundaryVertexTanhNormalizedSimonDenominator_eq_currentDenominator]
      using hcurrent
  calc
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v =
        Real.tanh (β * H) *
          boundaryVertexTanhNormalizedEmptyBoundaryTerm β H n v :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm_eq_tanh_mul_normalized
        hTne
    _ ≤
        Real.tanh (β * H) *
          (share * boundaryVertexTanhNormalizedSimonDenominator β H n v) :=
      mul_le_mul_of_nonneg_left hnormalized (le_of_lt hTpos)
    _ =
        share * finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
          β H n v := by
      rw [
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_eq_tanh_mul_normalized
          hvbdry]
      ring


theorem componentShares_of_nonneg_sum_le
    {one boundary empty D : ℝ}
    (hD : 0 ≤ D)
    (hone : 0 ≤ one)
    (hboundary : 0 ≤ boundary)
    (hempty : 0 ≤ empty)
    (hsum : one + boundary + empty ≤ D) :
    ∃ oneShare boundaryShare emptyShare : ℝ,
      0 ≤ oneShare ∧
      0 ≤ boundaryShare ∧
      0 ≤ emptyShare ∧
      oneShare + boundaryShare + emptyShare ≤ 1 ∧
      one ≤ oneShare * D ∧
      boundary ≤ boundaryShare * D ∧
      empty ≤ emptyShare * D := by
  by_cases hDpos : 0 < D
  · refine ⟨one / D, boundary / D, empty / D, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact div_nonneg hone hD
    · exact div_nonneg hboundary hD
    · exact div_nonneg hempty hD
    · calc
        one / D + boundary / D + empty / D =
            (one + boundary + empty) / D := by ring
        _ ≤ D / D := div_le_div_of_nonneg_right hsum (le_of_lt hDpos)
        _ = 1 := by field_simp [ne_of_gt hDpos]
    · exact le_of_eq (by field_simp [ne_of_gt hDpos])
    · exact le_of_eq (by field_simp [ne_of_gt hDpos])
    · exact le_of_eq (by field_simp [ne_of_gt hDpos])
  · have hDle : D ≤ 0 := le_of_not_gt hDpos
    have hDzero : D = 0 := le_antisymm hDle hD
    have hsum0 : one + boundary + empty ≤ 0 := by
      simpa [hDzero] using hsum
    have hone0 : one ≤ 0 := by linarith
    have hboundary0 : boundary ≤ 0 := by linarith
    have hempty0 : empty ≤ 0 := by linarith
    refine ⟨0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · simpa [hDzero] using hone0
    · simpa [hDzero] using hboundary0
    · simpa [hDzero] using hempty0

set_option linter.style.longLine false in


theorem three_ratio_sum_lt_one_iff_sum_lt_of_pos
    {one boundary empty D : ℝ} (hDpos : 0 < D) :
    one / D + boundary / D + empty / D < 1 ↔
      one + boundary + empty < D := by
  constructor
  · intro hratio
    have hmul :
        (one / D + boundary / D + empty / D) * D < 1 * D :=
      mul_lt_mul_of_pos_right hratio hDpos
    have hleft :
        (one / D + boundary / D + empty / D) * D =
          one + boundary + empty := by
      field_simp [hDpos.ne']
    simpa [hleft] using hmul
  · intro hsum
    calc
      one / D + boundary / D + empty / D =
          (one + boundary + empty) / D := by
        ring
      _ < D / D := div_lt_div_of_pos_right hsum hDpos
      _ = 1 := by
        field_simp [hDpos.ne']

set_option linter.style.longLine false in


theorem four_ratio_sum_le_one_iff_sum_le_of_pos
    {one boundary empty shell D : ℝ} (hDpos : 0 < D) :
    one / D + boundary / D + empty / D + shell / D ≤ 1 ↔
      one + boundary + empty + shell ≤ D := by
  constructor
  · intro hratio
    have hmul :
        (one / D + boundary / D + empty / D + shell / D) * D ≤
          1 * D :=
      mul_le_mul_of_nonneg_right hratio (le_of_lt hDpos)
    have hleft :
        (one / D + boundary / D + empty / D + shell / D) * D =
          one + boundary + empty + shell := by
      field_simp [hDpos.ne']
    simpa [hleft] using hmul
  · intro hsum
    calc
      one / D + boundary / D + empty / D + shell / D =
          (one + boundary + empty + shell) / D := by
        ring
      _ ≤ D / D := div_le_div_of_nonneg_right hsum (le_of_lt hDpos)
      _ = 1 := by
        field_simp [hDpos.ne']

set_option linter.style.longLine false in


theorem four_ratio_sum_lt_one_iff_sum_lt_of_pos
    {one boundary empty shell D : ℝ} (hDpos : 0 < D) :
    one / D + boundary / D + empty / D + shell / D < 1 ↔
      one + boundary + empty + shell < D := by
  constructor
  · intro hratio
    have hmul :
        (one / D + boundary / D + empty / D + shell / D) * D <
          1 * D :=
      mul_lt_mul_of_pos_right hratio hDpos
    have hleft :
        (one / D + boundary / D + empty / D + shell / D) * D =
          one + boundary + empty + shell := by
      field_simp [hDpos.ne']
    simpa [hleft] using hmul
  · intro hsum
    calc
      one / D + boundary / D + empty / D + shell / D =
          (one + boundary + empty + shell) / D := by
        ring
      _ < D / D := div_lt_div_of_pos_right hsum hDpos
      _ = 1 := by
        field_simp [hDpos.ne']


theorem fourShares_of_nonneg_sum_le
    {one boundary empty coefficient D : ℝ}
    (hD : 0 ≤ D)
    (hone : 0 ≤ one)
    (hboundary : 0 ≤ boundary)
    (hempty : 0 ≤ empty)
    (hcoefficient : 0 ≤ coefficient)
    (hsum : one + boundary + empty + coefficient ≤ D) :
    ∃ oneShare boundaryShare emptyShare coefficientShare : ℝ,
      0 ≤ oneShare ∧
      0 ≤ boundaryShare ∧
      0 ≤ emptyShare ∧
      0 ≤ coefficientShare ∧
      oneShare + boundaryShare + emptyShare + coefficientShare ≤ 1 ∧
      one ≤ oneShare * D ∧
      boundary ≤ boundaryShare * D ∧
      empty ≤ emptyShare * D ∧
      coefficient ≤ coefficientShare * D := by
  by_cases hDpos : 0 < D
  · refine
      ⟨one / D, boundary / D, empty / D, coefficient / D,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact div_nonneg hone hD
    · exact div_nonneg hboundary hD
    · exact div_nonneg hempty hD
    · exact div_nonneg hcoefficient hD
    · calc
        one / D + boundary / D + empty / D + coefficient / D =
            (one + boundary + empty + coefficient) / D := by
          ring
        _ ≤ D / D := div_le_div_of_nonneg_right hsum (le_of_lt hDpos)
        _ = 1 := by
          field_simp [ne_of_gt hDpos]
    · exact le_of_eq (by field_simp [ne_of_gt hDpos])
    · exact le_of_eq (by field_simp [ne_of_gt hDpos])
    · exact le_of_eq (by field_simp [ne_of_gt hDpos])
    · exact le_of_eq (by field_simp [ne_of_gt hDpos])
  · have hDle : D ≤ 0 := le_of_not_gt hDpos
    have hDzero : D = 0 := le_antisymm hDle hD
    have hsum0 : one + boundary + empty + coefficient ≤ 0 := by
      simpa [hDzero] using hsum
    have hone0 : one ≤ 0 := by linarith
    have hboundary0 : boundary ≤ 0 := by linarith
    have hempty0 : empty ≤ 0 := by linarith
    have hcoefficient0 : coefficient ≤ 0 := by linarith
    refine ⟨0, 0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · simpa [hDzero] using hone0
    · simpa [hDzero] using hboundary0
    · simpa [hDzero] using hempty0
    · simpa [hDzero] using hcoefficient0


theorem twoShares_of_nonneg_sum_le
    {combined empty D : ℝ}
    (hD : 0 ≤ D)
    (hcombined : 0 ≤ combined)
    (hempty : 0 ≤ empty)
    (hsum : combined + empty ≤ D) :
    ∃ combinedShare emptyShare : ℝ,
      0 ≤ combinedShare ∧
      0 ≤ emptyShare ∧
      combinedShare + emptyShare ≤ 1 ∧
      combined ≤ combinedShare * D ∧
      empty ≤ emptyShare * D := by
  by_cases hDpos : 0 < D
  · refine ⟨combined / D, empty / D, ?_, ?_, ?_, ?_, ?_⟩
    · exact div_nonneg hcombined hD
    · exact div_nonneg hempty hD
    · calc
        combined / D + empty / D = (combined + empty) / D := by
          ring
        _ ≤ D / D := div_le_div_of_nonneg_right hsum (le_of_lt hDpos)
        _ = 1 := by
          field_simp [ne_of_gt hDpos]
    · exact le_of_eq (by field_simp [ne_of_gt hDpos])
    · exact le_of_eq (by field_simp [ne_of_gt hDpos])
  · have hDle : D ≤ 0 := le_of_not_gt hDpos
    have hDzero : D = 0 := le_antisymm hDle hD
    have hsum0 : combined + empty ≤ 0 := by
      simpa [hDzero] using hsum
    have hcombined0 : combined ≤ 0 := by linarith
    have hempty0 : empty ≤ 0 := by linarith
    refine ⟨0, 0, ?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · simpa [hDzero] using hcombined0
    · simpa [hDzero] using hempty0


theorem boundaryCrossingCapComponentSumAbsorption_of_cappedComponentBudget
    (h : BoundaryCrossingCapCappedBudgetPositiveSubcritical) :
    BoundaryCrossingCapComponentSumPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  rcases hn H hH Ω v hv with
    ⟨oneBudget, boundaryPairBudget, emptyBoundaryBudget,
      hone, hboundary, hempty, htotal⟩
  calc
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n +
        cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
        ≤ oneBudget + boundaryPairBudget + emptyBoundaryBudget := by
          exact add_le_add (add_le_add hone hboundary) hempty
    _ ≤ finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v :=
      htotal

end Exact3D
end StatMech
