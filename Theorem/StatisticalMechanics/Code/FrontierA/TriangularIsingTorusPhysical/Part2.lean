/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusShiftedAssembly
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorSandwich.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical
open scoped BigOperators
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Onsager

@[simp] theorem triangularTorusRealEdgeWeight_cast
    (L : Nat) (t1 t2 t3 : Real)
    (edge : Sym2 (ZMod L × ZMod L)) :
    (triangularTorusRealEdgeWeight L t1 t2 t3 edge : Complex) =
      triangularTorusEdgeWeight L t1 t2 t3 edge := by
  by_cases hhorizontal : squareTorusHorizontalEdge L edge
  · simp [triangularTorusRealEdgeWeight, triangularTorusEdgeWeight,
      hhorizontal]
  · by_cases hvertical : triangularTorusVerticalEdge L edge
    · simp [triangularTorusRealEdgeWeight, triangularTorusEdgeWeight,
        hhorizontal, hvertical]
    · simp [triangularTorusRealEdgeWeight, triangularTorusEdgeWeight,
        hhorizontal, hvertical]

theorem real_tanh_nonneg {x : Real} (hx : 0 ≤ x) :
    0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le


theorem triangularTorusNormalizedEvenSubgraph_log_sandwich
    (L : Nat) [Fact (2 < L)]
    (J1 J2 J3 : Real) (rho : Complex)
    (hJ1 : 0 ≤ J1) (hJ2 : 0 ≤ J2) (hJ3 : 0 ≤ J3) :
    let C := (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L)
    let weight := triangularTorusRealEdgeWeight L
      (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)
    let sector : Fin 2 -> Fin 2 -> Complex := fun a b =>
      (C : Complex) * triangularTorusWeightedSpinCharacterSum L
        (fun edge => (weight edge : Complex)) a b
    Real.log (arfSectorNormMax sector) ≤
        Real.log (C *
          inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight) ∧
      Real.log (C *
          inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight) ≤
        Real.log (arfSectorNormMax sector) + Real.log 2 := by
  dsimp only
  let weight := triangularTorusRealEdgeWeight L
    (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)
  let C := (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L)
  let E := inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight
  let sector : Fin 2 -> Fin 2 -> Complex := fun a b =>
    (C : Complex) * triangularTorusWeightedSpinCharacterSum L
      (fun edge => (weight edge : Complex)) a b
  have hweight : forall edge, 0 ≤ weight edge := by
    intro edge
    by_cases hhorizontal : squareTorusHorizontalEdge L edge
    · simp [weight, triangularTorusRealEdgeWeight, hhorizontal,
        real_tanh_nonneg hJ1]
    · by_cases hvertical : triangularTorusVerticalEdge L edge
      · simp [weight, triangularTorusRealEdgeWeight, hhorizontal, hvertical,
          real_tanh_nonneg hJ2]
      · simp [weight, triangularTorusRealEdgeWeight, hhorizontal, hvertical,
          real_tanh_nonneg hJ3]
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hE : 0 < E :=
    inhomogeneousEvenSubgraphSum_pos_of_nonneg
      (triangularTorusGraph L) weight hweight
  apply arfSector_log_sandwich (C * E) sector (mul_pos hC hE)
  · intro a b
    dsimp only [sector]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    exact mul_le_mul_of_nonneg_left
      (triangularTorusWeightedSpin_norm_le_evenSubgraphSum
        L hweight a b) hC.le
  · have harf := two_mul_triangularTorusEvenSubgraphSum_eq_spin L weight
    change (2 : Complex) * (E : Complex) = _ at harf
    dsimp only [sector]
    calc
      ((2 * (C * E) : Real) : Complex) = (C : Complex) * (2 * E) := by
        push_cast
        ring
      _ = (C : Complex) *
          (triangularTorusWeightedSpinCharacterSum L
              (fun edge => (weight edge : Complex)) 1 1 +
            triangularTorusWeightedSpinCharacterSum L
              (fun edge => (weight edge : Complex)) 0 1 +
            triangularTorusWeightedSpinCharacterSum L
              (fun edge => (weight edge : Complex)) 1 0 -
            triangularTorusWeightedSpinCharacterSum L
              (fun edge => (weight edge : Complex)) 0 0) := by rw [harf]
      _ = _ := by ring


theorem triangularTorusNormalizedSector_logDensity_tendsto
    (J1 J2 J3 : Real) (rho : Complex) (a b : Fin 2)
    (hrho : rho ^ 4 = Complex.I)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun n : Nat =>
        Real.log ‖triangularTorusNormalizedSectorSequence
          J1 J2 J3 rho a b n‖ / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
  have hgrid := triangularIsingSymbol_riemann_tendsto_spinShift
    J1 J2 J3 a b hpos
  have hshift := hgrid.comp (Filter.tendsto_add_atTop_nat 3)
  have hscaled := (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Nat => (1 / (8 * Real.pi ^ 2) : Real))
      Filter.atTop (nhds (1 / (8 * Real.pi ^ 2)))).mul hshift
  apply hscaled.congr'
  filter_upwards [] with n
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  letI : NeZero L := ⟨by dsimp only [L]; omega⟩
  dsimp only [Function.comp_apply]
  simp only [triangularTorusNormalizedSectorSequence]
  rw [triangularTorus_normalizedSector_log_norm_eq
    (n + 3) J1 J2 J3 rho a b hrho hpos]
  have hsum := sum_zmod_prod_eq_sum_range (n + 3) (fun i j =>
    Real.log (triangularIsingSymbol J1 J2 J3
      (2 * Real.pi * (i + (a.val : Real) / 2) / (n + 3))
      (2 * Real.pi * (j + (b.val : Real) / 2) / (n + 3))))
  have hsum' :
      (∑ j : ZMod (n + 3) × ZMod (n + 3),
        Real.log (triangularIsingSymbol J1 J2 J3
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / (n + 3))
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / (n + 3)))) =
        ∑ i ∈ Finset.range (n + 3), ∑ j ∈ Finset.range (n + 3),
          Real.log (triangularIsingSymbol J1 J2 J3
            (2 * Real.pi * (i + (a.val : Real) / 2) / (n + 3))
            (2 * Real.pi * (j + (b.val : Real) / 2) / (n + 3))) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hsum
  simp only [Nat.cast_add, Nat.cast_ofNat]
  rw [hsum']
  have hL : (L : Real) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring


theorem triangularTorusNormalizedSectorMax_logDensity_tendsto
    (J1 J2 J3 : Real) (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun n : Nat =>
        Real.log (triangularTorusNormalizedSectorMaxSequence
          J1 J2 J3 rho n) / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
  let limit : Real := (1 / (8 * Real.pi ^ 2)) *
    ∫ k1 in (-Real.pi)..Real.pi,
      ∫ k2 in (-Real.pi)..Real.pi,
        Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)
  have h11 := triangularTorusNormalizedSector_logDensity_tendsto
    J1 J2 J3 rho 1 1 hrho hpos
  have h01 := triangularTorusNormalizedSector_logDensity_tendsto
    J1 J2 J3 rho 0 1 hrho hpos
  have h10 := triangularTorusNormalizedSector_logDensity_tendsto
    J1 J2 J3 rho 1 0 hrho hpos
  have h00 := triangularTorusNormalizedSector_logDensity_tendsto
    J1 J2 J3 rho 0 0 hrho hpos
  have hmax := (h11.max h01).max (h10.max h00)
  have hmax' : Filter.Tendsto
      (fun n : Nat =>
        max
          (max
            (Real.log ‖triangularTorusNormalizedSectorSequence
                J1 J2 J3 rho 1 1 n‖ / (n + 3 : Real) ^ 2)
            (Real.log ‖triangularTorusNormalizedSectorSequence
                J1 J2 J3 rho 0 1 n‖ / (n + 3 : Real) ^ 2))
          (max
            (Real.log ‖triangularTorusNormalizedSectorSequence
                J1 J2 J3 rho 1 0 n‖ / (n + 3 : Real) ^ 2)
            (Real.log ‖triangularTorusNormalizedSectorSequence
                J1 J2 J3 rho 0 0 n‖ / (n + 3 : Real) ^ 2)))
      Filter.atTop (nhds limit) := by
    simpa only [max_self] using hmax
  apply hmax'.congr'
  filter_upwards [] with n
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  let sector : Fin 2 -> Fin 2 -> Complex := fun a b =>
    triangularTorusNormalizedSectorSequence J1 J2 J3 rho a b n
  have hsector (a b : Fin 2) : 0 < ‖sector a b‖ := by
    rw [norm_pos_iff]
    dsimp only [sector, triangularTorusNormalizedSectorSequence]
    exact triangularTorus_normalizedSector_ne_zero
      L J1 J2 J3 rho a b hrho hpos
  have hlogmax (x y : Real) (hx : 0 < x) (hy : 0 < y) :
      Real.log (max x y) = max (Real.log x) (Real.log y) :=
    Real.strictMonoOn_log.monotoneOn.map_max hx hy
  have hden : 0 ≤ (n + 3 : Real) ^ 2 := sq_nonneg _
  dsimp only [triangularTorusNormalizedSectorMaxSequence,
    arfSectorNormMax]
  rw [hlogmax _ _ (lt_of_lt_of_le (hsector 1 1) (le_max_left _ _))
      (lt_of_lt_of_le (hsector 1 0) (le_max_left _ _)),
    hlogmax _ _ (hsector 1 1) (hsector 0 1),
    hlogmax _ _ (hsector 1 0) (hsector 0 0),
    max_div_div_right hden, max_div_div_right hden,
    max_div_div_right hden]

theorem triangularTorusEdgeWeight_real_cast
    (L : Nat) (x y z : Real) :
    (fun edge => (triangularTorusRealEdgeWeight L x y z edge : Complex)) =
      triangularTorusEdgeWeight L x y z := by
  funext edge
  by_cases hx : squareTorusHorizontalEdge L edge
  · simp [triangularTorusRealEdgeWeight, triangularTorusEdgeWeight, hx]
  · by_cases hy : triangularTorusVerticalEdge L edge
    · simp [triangularTorusRealEdgeWeight, triangularTorusEdgeWeight,
        hx, hy]
    · simp [triangularTorusRealEdgeWeight, triangularTorusEdgeWeight,
        hx, hy]

theorem triangularTorusRealEdgeWeight_nonneg
    (L : Nat) {x y z : Real} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ∀ edge, 0 ≤ triangularTorusRealEdgeWeight L x y z edge := by
  intro edge
  unfold triangularTorusRealEdgeWeight
  split_ifs <;> assumption

theorem arfSectorNormMax_nonneg_real_mul
    (c : Real) (hc : 0 ≤ c)
    (sector : Fin 2 → Fin 2 → Complex) :
    arfSectorNormMax (fun a b => (c : Complex) * sector a b) =
      c * arfSectorNormMax sector := by
  simp only [arfSectorNormMax, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hc]
  rw [mul_max_of_nonneg _ _ hc, mul_max_of_nonneg _ _ hc,
    mul_max_of_nonneg _ _ hc]


end StatMech.FrontierA
