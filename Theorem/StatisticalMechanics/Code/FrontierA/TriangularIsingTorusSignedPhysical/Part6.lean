/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSignedPhysical.Part6
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem two_mul_triangularTorusNormalizedQuadraticSector_eq_walsh
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (a b : Fin 2) :
    (2 : Complex) *
        triangularTorusNormalizedQuadraticSector L J1 J2 J3 a b =
      ∑ chi : Fin 2 × Fin 2,
        (triangularTorusQuadraticWalshSign a b chi : Complex) *
          triangularTorusNormalizedLinearSector L J1 J2 J3 chi := by
  let C : Real :=
    (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L)
  have hw := two_mul_triangularTorusWeightedSpinCharacterSum_eq_walsh
    L (triangularTorusRealEdgeWeight L
      (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b
  unfold triangularTorusNormalizedQuadraticSector
    triangularTorusNormalizedLinearSector
  rw [← triangularTorusEdgeWeight_real_cast]
  have hscaled := congrArg (fun z : Complex => (C : Complex) * z) hw
  dsimp only at hscaled
  rw [Finset.mul_sum] at hscaled
  convert hscaled using 1
  · ring
  · apply Finset.sum_congr rfl
    intro chi hchi
    norm_cast
    ring


theorem norm_triangularTorusNormalizedQuadraticSector_le
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (a b : Fin 2) :
    ‖triangularTorusNormalizedQuadraticSector L J1 J2 J3 a b‖ ≤
      2 * Real.exp (8 * (|J1| + |J2| + |J3|) * L) *
        triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) := by
  let Q := triangularTorusNormalizedQuadraticSector L J1 J2 J3 a b
  let P := triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0)
  let R := Real.exp (8 * (|J1| + |J2| + |J3|) * L) * P
  have hw := two_mul_triangularTorusNormalizedQuadraticSector_eq_walsh
    L J1 J2 J3 a b
  have hsum :
      ‖∑ chi : Fin 2 × Fin 2,
        (triangularTorusQuadraticWalshSign a b chi : Complex) *
          triangularTorusNormalizedLinearSector L J1 J2 J3 chi‖ ≤
        ∑ chi : Fin 2 × Fin 2,
          ‖(triangularTorusQuadraticWalshSign a b chi : Complex) *
            triangularTorusNormalizedLinearSector L J1 J2 J3 chi‖ :=
    norm_sum_le _ _
  have hterm (chi : Fin 2 × Fin 2) :
      ‖(triangularTorusQuadraticWalshSign a b chi : Complex) *
          triangularTorusNormalizedLinearSector L J1 J2 J3 chi‖ =
        triangularTorusNormalizedLinearSector L J1 J2 J3 chi := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have hsign : |triangularTorusQuadraticWalshSign a b chi| = 1 := by
      unfold triangularTorusQuadraticWalshSign
      rcases neg_one_pow_eq_or Real
          ((1 + a.val + chi.1.val) * (1 + b.val + chi.2.val)) with h | h <;>
        simp [h]
    rw [hsign, one_mul, abs_of_pos
      (triangularTorusNormalizedLinearSector_pos L J1 J2 J3 chi)]
  have hlinear (chi : Fin 2 × Fin 2) :
      triangularTorusNormalizedLinearSector L J1 J2 J3 chi ≤ R := by
    exact triangularTorusNormalizedLinearSector_le_exp_boundary_mul
      L J1 J2 J3 chi
  have hfour :
      (∑ _chi : Fin 2 × Fin 2, R) = 4 * R := by simp
  have hnorm : 2 * ‖Q‖ ≤ 4 * R := by
    calc
      2 * ‖Q‖ = ‖(2 : Complex) * Q‖ := by norm_num
      _ = ‖∑ chi : Fin 2 × Fin 2,
          (triangularTorusQuadraticWalshSign a b chi : Complex) *
            triangularTorusNormalizedLinearSector L J1 J2 J3 chi‖ := by
        rw [hw]
      _ ≤ ∑ chi : Fin 2 × Fin 2,
          ‖(triangularTorusQuadraticWalshSign a b chi : Complex) *
            triangularTorusNormalizedLinearSector L J1 J2 J3 chi‖ := hsum
      _ = ∑ chi : Fin 2 × Fin 2,
          triangularTorusNormalizedLinearSector L J1 J2 J3 chi := by
        apply Finset.sum_congr rfl
        intro chi hchi
        exact hterm chi
      _ ≤ ∑ _chi : Fin 2 × Fin 2, R :=
        Finset.sum_le_sum fun chi hchi => hlinear chi
      _ = 4 * R := hfour
  dsimp only [Q, R, P] at hnorm ⊢
  linarith


theorem two_mul_triangularTorusNormalizedLinearSector_zero_eq_arf
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real) :
    ((2 * triangularTorusNormalizedLinearSector
        L J1 J2 J3 (0, 0) : Real) : Complex) =
      triangularTorusNormalizedQuadraticSector L J1 J2 J3 1 1 +
        triangularTorusNormalizedQuadraticSector L J1 J2 J3 0 1 +
        triangularTorusNormalizedQuadraticSector L J1 J2 J3 1 0 -
        triangularTorusNormalizedQuadraticSector L J1 J2 J3 0 0 := by
  let C : Real :=
    (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L)
  let weight := triangularTorusRealEdgeWeight L
    (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)
  have harf := two_mul_triangularTorusEvenSubgraphSum_eq_spin L weight
  have hscaled := congrArg (fun z : Complex => (C : Complex) * z) harf
  dsimp only at hscaled
  rw [triangularTorusNormalizedLinearSector_zero]
  unfold triangularTorusNormalizedQuadraticSector
  rw [← triangularTorusEdgeWeight_real_cast]
  change (((2 * (C * inhomogeneousEvenSubgraphSum
    (triangularTorusGraph L) weight) : Real)) : Complex) = _
  convert hscaled using 1 <;> norm_cast <;> ring

theorem triangularTorusNormalizedLinearSector_zero_le_two_mul_max
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real) :
    triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) ≤
      2 * arfSectorNormMax
        (triangularTorusNormalizedQuadraticSector L J1 J2 J3) := by
  let P := triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0)
  let Q := triangularTorusNormalizedQuadraticSector L J1 J2 J3
  let M := arfSectorNormMax Q
  have hP : 0 < P :=
    triangularTorusNormalizedLinearSector_pos L J1 J2 J3 (0, 0)
  have harf :=
    two_mul_triangularTorusNormalizedLinearSector_zero_eq_arf L J1 J2 J3
  have hterm (a b : Fin 2) : ‖Q a b‖ ≤ M :=
    norm_le_arfSectorNormMax Q a b
  have hsum :
      ‖Q 1 1 + Q 0 1 + Q 1 0 - Q 0 0‖ ≤ 4 * M := by
    calc
      _ ≤ ‖Q 1 1 + Q 0 1 + Q 1 0‖ + ‖Q 0 0‖ := norm_sub_le _ _
      _ ≤ (‖Q 1 1 + Q 0 1‖ + ‖Q 1 0‖) + ‖Q 0 0‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖Q 1 1‖ + ‖Q 0 1‖) + ‖Q 1 0‖) + ‖Q 0 0‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ 4 * M := by
        nlinarith [hterm 1 1, hterm 0 1, hterm 1 0, hterm 0 0]
  have harfNorm := congrArg norm harf
  have hleft : ‖((2 * P : Real) : Complex)‖ = 2 * P := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hP)]
  rw [hleft] at harfNorm
  dsimp only [P, Q, M] at hsum harfNorm ⊢
  nlinarith [harfNorm.trans_le hsum]

theorem arfSectorNormMax_normalizedQuadratic_le
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real) :
    arfSectorNormMax
        (triangularTorusNormalizedQuadraticSector L J1 J2 J3) ≤
      2 * Real.exp (8 * (|J1| + |J2| + |J3|) * L) *
        triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) := by
  unfold arfSectorNormMax
  apply max_le
  · apply max_le <;>
      exact norm_triangularTorusNormalizedQuadraticSector_le L J1 J2 J3 _ _
  · apply max_le <;>
      exact norm_triangularTorusNormalizedQuadraticSector_le L J1 J2 J3 _ _


theorem triangularTorusSigned_normalized_log_gap_abs_le
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real) :
    |Real.log (triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0)) -
      Real.log (arfSectorNormMax
        (triangularTorusNormalizedQuadraticSector L J1 J2 J3))| ≤
      8 * (|J1| + |J2| + |J3|) * L + Real.log 2 := by
  let P := triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0)
  let M := arfSectorNormMax
    (triangularTorusNormalizedQuadraticSector L J1 J2 J3)
  let B : Real := 8 * (|J1| + |J2| + |J3|) * L
  have hP : 0 < P :=
    triangularTorusNormalizedLinearSector_pos L J1 J2 J3 (0, 0)
  have hPM : P ≤ 2 * M :=
    triangularTorusNormalizedLinearSector_zero_le_two_mul_max L J1 J2 J3
  have hM : 0 < M := by
    by_contra h
    have hnonpos := le_of_not_gt h
    nlinarith
  have hMP : M ≤ 2 * Real.exp B * P :=
    arfSectorNormMax_normalizedQuadratic_le L J1 J2 J3
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hlog_upper : Real.log P - Real.log M ≤ Real.log 2 := by
    have h := Real.log_le_log hP hPM
    rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hM.ne'] at h
    linarith
  have hlog_lower : -(B + Real.log 2) ≤ Real.log P - Real.log M := by
    have htwoexp : 0 < 2 * Real.exp B := mul_pos (by norm_num) (Real.exp_pos _)
    have h := Real.log_le_log hM hMP
    rw [Real.log_mul htwoexp.ne' hP.ne',
      Real.log_mul (by norm_num : (2 : Real) ≠ 0) (Real.exp_ne_zero B),
      Real.log_exp] at h
    linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  dsimp only [P, M, B] at hlog_upper hlog_lower hB ⊢
  rw [abs_le]
  constructor
  · exact hlog_lower
  · linarith

theorem triangularTorusNormalizedEvenSequence_eq_linear
    (J1 J2 J3 : Real) (n : Nat) :
    triangularTorusNormalizedEvenSequence J1 J2 J3 n =
      let L := n + 3
      letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
      triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  rw [triangularTorusNormalizedEvenSequence,
    triangularTorusNormalizedLinearSector_zero]

theorem triangularTorusNormalizedSectorMaxSequence_eq_quadratic
    (J1 J2 J3 : Real) (rho : Complex) (n : Nat) :
    triangularTorusNormalizedSectorMaxSequence J1 J2 J3 rho n =
      let L := n + 3
      letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
      arfSectorNormMax
        (triangularTorusNormalizedQuadraticSector L J1 J2 J3) := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  unfold triangularTorusNormalizedSectorMaxSequence
    triangularTorusNormalizedSectorSequence
    triangularTorusNormalizedQuadraticSector
  rfl

theorem triangularTorusSigned_normalizedSequence_log_gap_abs_le
    (J1 J2 J3 : Real) (rho : Complex) (n : Nat) :
    |Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) -
      Real.log (triangularTorusNormalizedSectorMaxSequence
        J1 J2 J3 rho n)| ≤
      8 * (|J1| + |J2| + |J3|) * (n + 3) + Real.log 2 := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  rw [triangularTorusNormalizedEvenSequence_eq_linear,
    triangularTorusNormalizedSectorMaxSequence_eq_quadratic]
  simpa only [L, Nat.cast_add, Nat.cast_ofNat] using
    (triangularTorusSigned_normalized_log_gap_abs_le L J1 J2 J3)


theorem triangularTorusSigned_normalized_log_gap_tendsto_zero
    (J1 J2 J3 : Real) (rho : Complex) :
    Filter.Tendsto
      (fun n : Nat =>
        (Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) -
          Real.log (triangularTorusNormalizedSectorMaxSequence
            J1 J2 J3 rho n)) / (n + 3 : Real) ^ 2)
      Filter.atTop (nhds 0) := by
  let A : Real := 8 * (|J1| + |J2| + |J3|)
  let upper : Nat → Real := fun n =>
    (A * (n + 3 : Real) + Real.log 2) / (n + 3 : Real) ^ 2
  have hrecip : Filter.Tendsto
      (fun n : Nat => (1 : Real) / (n + 3 : Real))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := Real)).comp
        (Filter.tendsto_add_atTop_nat 3)
  have hupper : Filter.Tendsto upper Filter.atTop (nhds 0) := by
    have h := ((tendsto_const_nhds : Filter.Tendsto
        (fun _ : Nat => A) Filter.atTop (nhds A)).mul hrecip).add
      ((tendsto_const_nhds : Filter.Tendsto
        (fun _ : Nat => Real.log 2) Filter.atTop (nhds (Real.log 2))).mul
          (hrecip.mul hrecip))
    convert h using 1
    funext n
    dsimp only [upper]
    have hn : (n + 3 : Real) ≠ 0 := by positivity
    field_simp
    ring
  have hlower : Filter.Tendsto (fun n => -upper n)
      Filter.atTop (nhds 0) := by
    simpa only [neg_zero] using hupper.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper ?_ ?_
  · intro n
    let gap := Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) -
      Real.log (triangularTorusNormalizedSectorMaxSequence J1 J2 J3 rho n)
    have habs := triangularTorusSigned_normalizedSequence_log_gap_abs_le
      J1 J2 J3 rho n
    have hden : 0 < (n + 3 : Real) ^ 2 := by positivity
    have hscaled : |gap / (n + 3 : Real) ^ 2| ≤ upper n := by
      rw [abs_div, abs_of_pos hden]
      dsimp only [gap, upper, A] at habs ⊢
      exact div_le_div_of_nonneg_right habs hden.le
    exact (abs_le.mp hscaled).1
  · intro n
    let gap := Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) -
      Real.log (triangularTorusNormalizedSectorMaxSequence J1 J2 J3 rho n)
    have habs := triangularTorusSigned_normalizedSequence_log_gap_abs_le
      J1 J2 J3 rho n
    have hden : 0 < (n + 3 : Real) ^ 2 := by positivity
    have hscaled : |gap / (n + 3 : Real) ^ 2| ≤ upper n := by
      rw [abs_div, abs_of_pos hden]
      dsimp only [gap, upper, A] at habs ⊢
      exact div_le_div_of_nonneg_right habs hden.le
    exact (abs_le.mp hscaled).2


theorem triangularTorusSignedNormalizedEven_logDensity_tendsto
    (J1 J2 J3 : Real) (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun n : Nat =>
        Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) /
          (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
  have hgap := triangularTorusSigned_normalized_log_gap_tendsto_zero
    J1 J2 J3 rho
  have hmax := triangularTorusNormalizedSectorMax_logDensity_tendsto
    J1 J2 J3 rho hrho hpos
  have hadd := hgap.add hmax
  have hadd' : Filter.Tendsto
      (fun n : Nat =>
        (Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) -
            Real.log (triangularTorusNormalizedSectorMaxSequence
              J1 J2 J3 rho n)) / (n + 3 : Real) ^ 2 +
          Real.log (triangularTorusNormalizedSectorMaxSequence
            J1 J2 J3 rho n) / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
    simpa only [zero_add] using hadd
  apply hadd'.congr'
  filter_upwards [] with n
  ring

theorem triangularTorusNormalizedEvenSequence_pos
    (J1 J2 J3 : Real) (n : Nat) :
    0 < triangularTorusNormalizedEvenSequence J1 J2 J3 n := by
  have hZ : 0 < triangularTorusIsingPartitionSequence J1 J2 J3 n := by
    unfold triangularTorusIsingPartitionSequence
    exact StatMech.Sharpness.ZJ_pos _ _ _
  rw [triangularTorusIsingPartitionSequence_eq] at hZ
  rcases mul_pos_iff.mp hZ with h | h
  · exact h.2
  · exfalso
    exact (not_lt_of_ge (by positivity)) h.1


theorem triangularTorusIsingPartition_freeEnergy_tendsto_signed
    (J1 J2 J3 : Real) (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun n : Nat =>
        -Real.log (triangularTorusIsingPartitionSequence J1 J2 J3 n) /
          (n + 3 : Real) ^ 2)
      Filter.atTop (nhds (triangularIsingFreeEnergyValue J1 J2 J3)) := by
  have heven := triangularTorusSignedNormalizedEven_logDensity_tendsto
    J1 J2 J3 rho hrho hpos
  have hlog2 : Filter.Tendsto
      (fun n : Nat =>
        Real.log (2 ^ ((n + 3) * (n + 3)) : Real) /
          (n + 3 : Real) ^ 2)
      Filter.atTop (nhds (Real.log 2)) := by
    have heq : ∀ n : Nat,
        Real.log (2 ^ ((n + 3) * (n + 3)) : Real) /
            (n + 3 : Real) ^ 2 = Real.log 2 := by
      intro n
      rw [Real.log_pow]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      field_simp
    exact (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Nat => Real.log 2) Filter.atTop (nhds (Real.log 2))).congr'
        (Filter.Eventually.of_forall fun n => (heq n).symm)
  have hneg := (hlog2.add heven).neg
  have hneg' : Filter.Tendsto
      (fun (x : Nat) =>
        -(Real.log (2 ^ ((x + 3) * (x + 3)) : Real) /
            (x + 3 : Real) ^ 2 +
          Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 x) /
            (x + 3 : Real) ^ 2))
      Filter.atTop (nhds (triangularIsingFreeEnergyValue J1 J2 J3)) := by
    convert hneg using 1 <;> unfold triangularIsingFreeEnergyValue <;> ring
  apply hneg'.congr'
  filter_upwards [] with n
  rw [triangularTorusIsingPartitionSequence_eq]
  have htwo : (2 ^ ((n + 3) * (n + 3)) : Real) ≠ 0 := by positivity
  have hevenPos := triangularTorusNormalizedEvenSequence_pos J1 J2 J3 n
  rw [Real.log_mul htwo hevenPos.ne']
  ring

theorem sum_abs_triangularTorusRealEdgeWeight_sub
    (L : Nat) [Fact (2 < L)]
    (J1 J2 J3 K1 K2 K3 : Real) :
    (∑ edge ∈ (triangularTorusGraph L).edgeFinset,
      |triangularTorusRealEdgeWeight L J1 J2 J3 edge -
        triangularTorusRealEdgeWeight L K1 K2 K3 edge|) =
      (L * L : Nat) * (|J1 - K1| + |J2 - K2| + |J3 - K3|) := by
  rw [sum_triangularPositiveEdgeSources L
    (triangularTorusGraph L).edgeFinset (fun _ hedge => hedge)
    (fun edge =>
      |triangularTorusRealEdgeWeight L J1 J2 J3 edge -
        triangularTorusRealEdgeWeight L K1 K2 K3 edge|)]
  simp_rw [triangularPositiveEdgeSources_edgeFinset,
    triangularTorusRealEdgeWeight_positiveEdge]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    ZMod.card, nsmul_eq_mul]
  rw [Fin.sum_univ_three]
  norm_num
  simp
  ring


theorem triangularTorusIsingPartition_freeEnergy_ray_lipschitz
    (J b c : Real) (n : Nat) :
    |(-Real.log (triangularTorusIsingPartitionSequence b b (b * J) n) /
          (n + 3 : Real) ^ 2) -
      (-Real.log (triangularTorusIsingPartitionSequence c c (c * J) n) /
          (n + 3 : Real) ^ 2)| ≤
      (2 + |J|) * |b - c| := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  have hlog := ZJ_log_coupling_sub_abs_le
    (triangularTorusGraph L).edgeFinset
    (triangularTorusRealEdgeWeight L b b (b * J))
    (triangularTorusRealEdgeWeight L c c (c * J))
  rw [sum_abs_triangularTorusRealEdgeWeight_sub] at hlog
  have hden : 0 < (n + 3 : Real) ^ 2 := by positivity
  have hdiff : |b * J - c * J| = |b - c| * |J| := by
    rw [← sub_mul, abs_mul]
  rw [hdiff] at hlog
  unfold triangularTorusIsingPartitionSequence
  rw [← sub_div, abs_div, abs_of_pos hden]
  calc
    |-Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
          (triangularTorusRealEdgeWeight L b b (b * J)) (fun _ => 0)) -
        -Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
          (triangularTorusRealEdgeWeight L c c (c * J)) (fun _ => 0))| /
        (n + 3 : Real) ^ 2 =
      |Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
          (triangularTorusRealEdgeWeight L c c (c * J)) (fun _ => 0)) -
        Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
          (triangularTorusRealEdgeWeight L b b (b * J)) (fun _ => 0))| /
        (n + 3 : Real) ^ 2 := by
      congr 2
      ring
    _ ≤
      ((L * L : Nat) *
        (|b - c| + |b - c| + |b - c| * |J|)) /
          (n + 3 : Real) ^ 2 := by
      apply div_le_div_of_nonneg_right _ hden.le
      simpa only [abs_sub_comm] using hlog
    _ = (2 + |J|) * |b - c| := by
      dsimp only [L]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      field_simp
      ring


theorem triangularTorusIsingPartition_freeEnergy_tendsto_critical
    {beta J : Real} (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hbeta : 0 < beta) (hJ : -1 < J)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    Filter.Tendsto
      (fun n : Nat =>
        -Real.log (triangularTorusIsingPartitionSequence
          beta beta (beta * J) n) / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds (triangularIsingFreeEnergyValue beta beta (beta * J))) := by
  let gamma : Nat → Real := fun m => beta + 1 / ((m : Real) + 1)
  let C : Real := 2 + |J|
  have hC : 0 < C := by dsimp only [C]; positivity
  have hgamma : Filter.Tendsto gamma Filter.atTop (nhds beta) := by
    simpa only [gamma, add_zero] using
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)))
  have hcontinuous : ContinuousAt
      (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta :=
    (triangularIsingFreeEnergyValue_contDiffAt_one_of_gt_neg_one_root
      hbeta hJ hroot).continuousAt
  have hvalue : Filter.Tendsto
      (fun m => triangularIsingFreeEnergyValue (gamma m) (gamma m)
        (gamma m * J)) Filter.atTop
      (nhds (triangularIsingFreeEnergyValue beta beta (beta * J))) :=
    hcontinuous.tendsto.comp hgamma
  obtain ⟨critical, hcritical, hcriticalUnique⟩ :=
    existsUnique_triangularIsingSymbol_zero_of_gt_neg_one hJ
  have hbetaZero : triangularIsingSymbol beta beta (beta * J) 0 0 = 0 :=
    (triangularIsingSymbol_zero_iff_criticalRate_eq_one hbeta).2 hroot
  have hbetaCritical : beta = critical :=
    hcriticalUnique beta ⟨hbeta, hbetaZero⟩
  rw [Metric.tendsto_atTop] at hvalue hgamma ⊢
  intro epsilon hepsilon
  obtain ⟨Nvalue, hNvalue⟩ := hvalue (epsilon / 3) (by positivity)
  obtain ⟨Ngamma, hNgamma⟩ := hgamma (epsilon / (3 * C)) (by positivity)
  let m := max Nvalue Ngamma
  have hmvalue :
      dist (triangularIsingFreeEnergyValue (gamma m) (gamma m) (gamma m * J))
        (triangularIsingFreeEnergyValue beta beta (beta * J)) < epsilon / 3 :=
    hNvalue m (le_max_left _ _)
  have hmgamma : dist (gamma m) beta < epsilon / (3 * C) :=
    hNgamma m (le_max_right _ _)
  have hgammapos : 0 < gamma m := by
    dsimp only [gamma]
    have hone : 0 < 1 / ((m : Real) + 1) := by positivity
    linarith
  have hgammanebeta : gamma m ≠ beta := by
    dsimp only [gamma]
    have hone : 0 < 1 / ((m : Real) + 1) := by positivity
    linarith
  have hgammanoncritical :
      triangularIsingCriticalRate (gamma m) (gamma m * J) ≠ 1 := by
    intro hgammaRoot
    have hgammaZero : triangularIsingSymbol (gamma m) (gamma m)
        (gamma m * J) 0 0 = 0 :=
      (triangularIsingSymbol_zero_iff_criticalRate_eq_one hgammapos).2
        hgammaRoot
    have hgammaCritical : gamma m = critical :=
      hcriticalUnique (gamma m) ⟨hgammapos, hgammaZero⟩
    exact hgammanebeta (hgammaCritical.trans hbetaCritical.symm)
  have hsymbol (p q : Real) :
      0 < triangularIsingSymbol (gamma m) (gamma m) (gamma m * J) p q :=
    triangularIsingSymbol_pos_of_gt_neg_one_noncritical
      hgammapos hJ hgammanoncritical p q
  have hfixed := triangularTorusIsingPartition_freeEnergy_tendsto_signed
    (gamma m) (gamma m) (gamma m * J) rho hrho hsymbol
  rw [Metric.tendsto_atTop] at hfixed
  obtain ⟨Nfixed, hNfixed⟩ := hfixed (epsilon / 3) (by positivity)
  refine ⟨Nfixed, fun n hn => ?_⟩
  have hmiddle := hNfixed n hn
  have hfinite := triangularTorusIsingPartition_freeEnergy_ray_lipschitz
    J beta (gamma m) n
  rw [Real.dist_eq] at hmiddle hmvalue hmgamma ⊢
  calc
    |-Real.log (triangularTorusIsingPartitionSequence
          beta beta (beta * J) n) / (n + 3 : Real) ^ 2 -
        triangularIsingFreeEnergyValue beta beta (beta * J)| ≤
      |(-Real.log (triangularTorusIsingPartitionSequence
          beta beta (beta * J) n) / (n + 3 : Real) ^ 2) -
        (-Real.log (triangularTorusIsingPartitionSequence
          (gamma m) (gamma m) (gamma m * J) n) / (n + 3 : Real) ^ 2)| +
      |(-Real.log (triangularTorusIsingPartitionSequence
          (gamma m) (gamma m) (gamma m * J) n) / (n + 3 : Real) ^ 2) -
        triangularIsingFreeEnergyValue (gamma m) (gamma m) (gamma m * J)| +
      |triangularIsingFreeEnergyValue (gamma m) (gamma m) (gamma m * J) -
        triangularIsingFreeEnergyValue beta beta (beta * J)| := by
      calc
        _ ≤ |(-Real.log (triangularTorusIsingPartitionSequence
            beta beta (beta * J) n) / (n + 3 : Real) ^ 2) -
              (-Real.log (triangularTorusIsingPartitionSequence
                (gamma m) (gamma m) (gamma m * J) n) /
                  (n + 3 : Real) ^ 2)| +
            |(-Real.log (triangularTorusIsingPartitionSequence
              (gamma m) (gamma m) (gamma m * J) n) /
                (n + 3 : Real) ^ 2) -
              triangularIsingFreeEnergyValue beta beta (beta * J)| :=
          abs_sub_le _ _ _
        _ ≤ _ := by
          have htriangle := abs_sub_le
            (-Real.log (triangularTorusIsingPartitionSequence
              (gamma m) (gamma m) (gamma m * J) n) /
                (n + 3 : Real) ^ 2)
            (triangularIsingFreeEnergyValue (gamma m) (gamma m) (gamma m * J))
            (triangularIsingFreeEnergyValue beta beta (beta * J))
          linarith
    _ < epsilon / 3 + epsilon / 3 + epsilon / 3 := by
      gcongr
      calc
        _ ≤ C * |beta - gamma m| := hfinite
        _ = C * |gamma m - beta| := by rw [abs_sub_comm]
        _ < C * (epsilon / (3 * C)) := by
          gcongr
        _ = epsilon / 3 := by field_simp
    _ = epsilon := by ring


theorem triangularTorusIsingPartition_freeEnergy_tendsto_gt_neg_one
    {beta J : Real} (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hbeta : 0 < beta) (hJ : -1 < J) :
    Filter.Tendsto
      (fun n : Nat =>
        -Real.log (triangularTorusIsingPartitionSequence
          beta beta (beta * J) n) / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds (triangularIsingFreeEnergyValue beta beta (beta * J))) := by
  by_cases hroot : triangularIsingCriticalRate beta (beta * J) = 1
  · exact triangularTorusIsingPartition_freeEnergy_tendsto_critical
      rho hrho hbeta hJ hroot
  · apply triangularTorusIsingPartition_freeEnergy_tendsto_signed
      beta beta (beta * J) rho hrho
    exact triangularIsingSymbol_pos_of_gt_neg_one_noncritical
      hbeta hJ hroot


theorem triangularTorusIsingPartition_freeEnergy_tendsto_le_neg_one
    {beta J : Real} (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hbeta : 0 < beta) (hJ : J ≤ -1) :
    Filter.Tendsto
      (fun n : Nat =>
        -Real.log (triangularTorusIsingPartitionSequence
          beta beta (beta * J) n) / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds (triangularIsingFreeEnergyValue beta beta (beta * J))) := by
  apply triangularTorusIsingPartition_freeEnergy_tendsto_signed
    beta beta (beta * J) rho hrho
  intro p q
  apply triangularIsingSymbol_pos_of_third_le_neg hbeta
  nlinarith [mul_le_mul_of_nonneg_left hJ hbeta.le]

end StatMech.FrontierA
