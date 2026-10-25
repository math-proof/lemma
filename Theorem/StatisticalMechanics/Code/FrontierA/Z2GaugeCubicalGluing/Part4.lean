/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSubsystem.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeRectangularThermodynamic
import Theorem.StatisticalMechanics.Code.FrontierA.RectangularBlockTiling
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part3
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.flexible false


namespace StatMech.FrontierA

noncomputable section

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

variable {Esmall Ebig Psmall Pbig : Type*}
  [Fintype Esmall] [DecidableEq Esmall] [Fintype Ebig] [DecidableEq Ebig]
  [Fintype Psmall] [DecidableEq Psmall] [Fintype Pbig] [DecidableEq Pbig]

theorem cubicalRectangularWilsonExpectation_mul_le_horizontal
    {beta : Real} (hbeta : 0 < beta) (m l n : Nat) :
    cubicalRectangularWilsonExpectation beta m n *
        cubicalRectangularWilsonExpectation beta l n ≤
      cubicalRectangularWilsonExpectation beta (m + l) n := by
  let c₁ := max m n
  let c₂ := max l n
  let C := max (m + l) n
  have hc₁ : c₁ ≤ C := by
    dsimp [c₁, C]
    apply max_le
    · exact le_trans (by omega) (Nat.le_max_left _ _)
    · exact Nat.le_max_right _ _
  have hc₂ : c₂ ≤ C := by
    dsimp [c₂, C]
    apply max_le
    · exact le_trans (by omega) (Nat.le_max_left _ _)
    · exact Nat.le_max_right _ _
  let E₁ := cubicalEdgeChart (a := m) (b := n) (c := c₁)
    (A := m + l) (B := n) (C := C) 0 0 0 (by omega) (by omega) (by omega)
  let E₂ := cubicalEdgeChart (a := l) (b := n) (c := c₂)
    (A := m + l) (B := n) (C := C) m 0 0 (by omega) (by omega) (by omega)
  let L₁ := (cubicalXYLoop (a := m) (b := n) (c := c₁)
    (0 : Fin (c₁ + 1))).map E₁
  let L₂ := (cubicalXYLoop (a := l) (b := n) (c := c₂)
    (0 : Fin (c₂ + 1))).map E₂
  have hleft : cubicalRectangularWilsonExpectation beta m n ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette (m + l) n C => beta) L₁ := by
    simpa [cubicalRectangularWilsonExpectation, c₁, C, E₁, L₁] using
      (cubicalXYWilsonExpectation_le_chart (a := m) (b := n) (c := c₁)
        (A := m + l) (B := n) (C := C) 0 0 0
        (by omega) (by omega) (by omega) hbeta.le (0 : Fin (c₁ + 1)))
  have hright : cubicalRectangularWilsonExpectation beta l n ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette (m + l) n C => beta) L₂ := by
    simpa [cubicalRectangularWilsonExpectation, c₂, C, E₂, L₂] using
      (cubicalXYWilsonExpectation_le_chart (a := l) (b := n) (c := c₂)
        (A := m + l) (B := n) (C := C) m 0 0
        (by omega) (by omega) (by omega) hbeta.le (0 : Fin (c₂ + 1)))
  have hsmall₂ : 0 ≤ cubicalRectangularWilsonExpectation beta l n :=
    (gaugeWilsonExpectation_mem_Icc cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette l n (max l n) => beta) (fun _ => hbeta)
      (cubicalXYLoop (0 : Fin (max l n + 1)))).1
  have hcommon₁ : 0 ≤ gaugeWilsonExpectation cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette (m + l) n C => beta) L₁ :=
    (gaugeWilsonExpectation_mem_Icc cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette (m + l) n C => beta) (fun _ => hbeta) L₁).1
  have hproduct : cubicalRectangularWilsonExpectation beta m n *
      cubicalRectangularWilsonExpectation beta l n ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette (m + l) n C => beta) L₁ *
        gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette (m + l) n C => beta) L₂ :=
    mul_le_mul hleft hright hsmall₂ hcommon₁
  have hgks := gaugeWilsonExpectation_mul_le_symmDiff
    cubicalPlaquetteIncidence
    (fun _ : CubicalPlaquette (m + l) n C => beta) (fun _ => hbeta.le) L₁ L₂
  have hloops : L₁ ∆ L₂ =
      cubicalXYLoop (a := m + l) (b := n) (c := C) (0 : Fin (C + 1)) := by
    simpa [c₁, c₂, C, E₁, E₂, L₁, L₂] using
      cubicalXYLoop_horizontal_symmDiff m l n c₁ c₂ C hc₁ hc₂
  rw [hloops] at hgks
  exact hproduct.trans (by
    simpa [cubicalRectangularWilsonExpectation, C] using hgks)

theorem cubicalRectangularWilsonExpectation_mul_le_vertical
    {beta : Real} (hbeta : 0 < beta) (m n k : Nat) :
    cubicalRectangularWilsonExpectation beta m n *
        cubicalRectangularWilsonExpectation beta m k ≤
      cubicalRectangularWilsonExpectation beta m (n + k) := by
  let c₁ := max m n
  let c₂ := max m k
  let C := max m (n + k)
  have hc₁ : c₁ ≤ C := by
    dsimp [c₁, C]
    apply max_le
    · exact Nat.le_max_left _ _
    · exact le_trans (by omega) (Nat.le_max_right _ _)
  have hc₂ : c₂ ≤ C := by
    dsimp [c₂, C]
    apply max_le
    · exact Nat.le_max_left _ _
    · exact le_trans (by omega) (Nat.le_max_right _ _)
  let E₁ := cubicalEdgeChart (a := m) (b := n) (c := c₁)
    (A := m) (B := n + k) (C := C) 0 0 0 (by omega) (by omega) (by omega)
  let E₂ := cubicalEdgeChart (a := m) (b := k) (c := c₂)
    (A := m) (B := n + k) (C := C) 0 n 0 (by omega) (by omega) (by omega)
  let L₁ := (cubicalXYLoop (a := m) (b := n) (c := c₁)
    (0 : Fin (c₁ + 1))).map E₁
  let L₂ := (cubicalXYLoop (a := m) (b := k) (c := c₂)
    (0 : Fin (c₂ + 1))).map E₂
  have hfirst : cubicalRectangularWilsonExpectation beta m n ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette m (n + k) C => beta) L₁ := by
    simpa [cubicalRectangularWilsonExpectation, c₁, C, E₁, L₁] using
      (cubicalXYWilsonExpectation_le_chart (a := m) (b := n) (c := c₁)
        (A := m) (B := n + k) (C := C) 0 0 0
        (by omega) (by omega) (by omega) hbeta.le (0 : Fin (c₁ + 1)))
  have hsecond : cubicalRectangularWilsonExpectation beta m k ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette m (n + k) C => beta) L₂ := by
    simpa [cubicalRectangularWilsonExpectation, c₂, C, E₂, L₂] using
      (cubicalXYWilsonExpectation_le_chart (a := m) (b := k) (c := c₂)
        (A := m) (B := n + k) (C := C) 0 n 0
        (by omega) (by omega) (by omega) hbeta.le (0 : Fin (c₂ + 1)))
  have hsmall₂ : 0 ≤ cubicalRectangularWilsonExpectation beta m k :=
    (gaugeWilsonExpectation_mem_Icc cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette m k (max m k) => beta) (fun _ => hbeta)
      (cubicalXYLoop (0 : Fin (max m k + 1)))).1
  have hcommon₁ : 0 ≤ gaugeWilsonExpectation cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette m (n + k) C => beta) L₁ :=
    (gaugeWilsonExpectation_mem_Icc cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette m (n + k) C => beta) (fun _ => hbeta) L₁).1
  have hproduct : cubicalRectangularWilsonExpectation beta m n *
      cubicalRectangularWilsonExpectation beta m k ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette m (n + k) C => beta) L₁ *
        gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette m (n + k) C => beta) L₂ :=
    mul_le_mul hfirst hsecond hsmall₂ hcommon₁
  have hgks := gaugeWilsonExpectation_mul_le_symmDiff
    cubicalPlaquetteIncidence
    (fun _ : CubicalPlaquette m (n + k) C => beta) (fun _ => hbeta.le) L₁ L₂
  have hloops : L₁ ∆ L₂ =
      cubicalXYLoop (a := m) (b := n + k) (c := C) (0 : Fin (C + 1)) := by
    simpa [c₁, c₂, C, E₁, E₂, L₁, L₂] using
      cubicalXYLoop_vertical_symmDiff m n k c₁ c₂ C hc₁ hc₂
  rw [hloops] at hgks
  exact hproduct.trans (by
    simpa [cubicalRectangularWilsonExpectation, C] using hgks)

@[simp] theorem gaugeWilsonExpectation_empty
    {E P : Type*} [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P]
    (incidence : P → Finset E) (K : P → Real) :
    gaugeWilsonExpectation incidence K ∅ = 1 := by
  unfold gaugeWilsonExpectation gaugeWilsonNumerator wilsonSpin
  simp only [Finset.prod_empty, one_mul]
  exact div_self (gaugePartition_pos incidence K).ne'

@[simp] theorem cubicalRectangularWilsonExpectation_zero_left
    (beta : Real) (n : Nat) :
    cubicalRectangularWilsonExpectation beta 0 n = 1 := by
  have hsheet : cubicalXYSheet (a := 0) (b := n) (c := max 0 n)
      (0 : Fin (max 0 n + 1)) = ∅ := by
    simp [cubicalXYSheet]
  have hloop : cubicalXYLoop (a := 0) (b := n) (c := max 0 n)
      (0 : Fin (max 0 n + 1)) = ∅ := by
    unfold cubicalXYLoop
    rw [hsheet]
    simp [gaugeSurfaceBoundary]
  simp [cubicalRectangularWilsonExpectation, hloop]

@[simp] theorem cubicalRectangularWilsonExpectation_zero_right
    (beta : Real) (m : Nat) :
    cubicalRectangularWilsonExpectation beta m 0 = 1 := by
  have hsheet : cubicalXYSheet (a := m) (b := 0) (c := max m 0)
      (0 : Fin (max m 0 + 1)) = ∅ := by
    simp [cubicalXYSheet]
  have hloop : cubicalXYLoop (a := m) (b := 0) (c := max m 0)
      (0 : Fin (max m 0 + 1)) = ∅ := by
    unfold cubicalXYLoop
    rw [hsheet]
    simp [gaugeSurfaceBoundary]
  simp [cubicalRectangularWilsonExpectation, hloop]

theorem cubicalRectangularWilsonExpectation_pos
    {beta : Real} (hbeta : 0 < beta) (m n : Nat) :
    0 < cubicalRectangularWilsonExpectation beta m n := by
  unfold cubicalRectangularWilsonExpectation
  apply (gaugeWilsonExpectation_pos_iff_exists_boundary
    cubicalPlaquetteIncidence
    (fun _ : CubicalPlaquette m n (max m n) => beta) (fun _ => hbeta)
    (cubicalXYLoop (0 : Fin (max m n + 1)))).mpr
  exact ⟨cubicalXYSheet (0 : Fin (max m n + 1)),
    cubicalXYSheet_hasWilsonBoundary (0 : Fin (max m n + 1))⟩

theorem cubicalRectangularWilsonFreeEnergy_eq_neg_log_expectation
    (beta : Real) (m n : Nat) :
    cubicalRectangularWilsonFreeEnergy beta m n =
      -Real.log (cubicalRectangularWilsonExpectation beta m n) := rfl

theorem cubicalRectangularWilsonFreeEnergy_horizontal_subadditive
    {beta : Real} (hbeta : 0 < beta) :
    HorizontallySubadditive (cubicalRectangularWilsonFreeEnergy beta) := by
  intro n m l
  have hm := cubicalRectangularWilsonExpectation_pos hbeta m n
  have hl := cubicalRectangularWilsonExpectation_pos hbeta l n
  have hprod := cubicalRectangularWilsonExpectation_mul_le_horizontal
    hbeta m l n
  have hlog := Real.log_le_log (mul_pos hm hl) hprod
  rw [Real.log_mul hm.ne' hl.ne'] at hlog
  simp only [cubicalRectangularWilsonFreeEnergy_eq_neg_log_expectation]
  linarith

theorem cubicalRectangularWilsonFreeEnergy_vertical_subadditive
    {beta : Real} (hbeta : 0 < beta) :
    VerticallySubadditive (cubicalRectangularWilsonFreeEnergy beta) := by
  intro m n k
  have hn := cubicalRectangularWilsonExpectation_pos hbeta m n
  have hk := cubicalRectangularWilsonExpectation_pos hbeta m k
  have hprod := cubicalRectangularWilsonExpectation_mul_le_vertical
    hbeta m n k
  have hlog := Real.log_le_log (mul_pos hn hk) hprod
  rw [Real.log_mul hn.ne' hk.ne'] at hlog
  simp only [cubicalRectangularWilsonFreeEnergy_eq_neg_log_expectation]
  linarith

theorem cubicalRectangularWilsonFreeEnergy_separatelySubadditive
    {beta : Real} (hbeta : 0 < beta) :
    SeparatelySubadditive (cubicalRectangularWilsonFreeEnergy beta) :=
  ⟨cubicalRectangularWilsonFreeEnergy_horizontal_subadditive hbeta,
    cubicalRectangularWilsonFreeEnergy_vertical_subadditive hbeta⟩

@[simp] theorem cubicalRectangularWilsonFreeEnergy_zero_left
    (beta : Real) (n : Nat) :
    cubicalRectangularWilsonFreeEnergy beta 0 n = 0 := by
  rw [cubicalRectangularWilsonFreeEnergy_eq_neg_log_expectation,
    cubicalRectangularWilsonExpectation_zero_left]
  norm_num

@[simp] theorem cubicalRectangularWilsonFreeEnergy_zero_right
    (beta : Real) (m : Nat) :
    cubicalRectangularWilsonFreeEnergy beta m 0 = 0 := by
  rw [cubicalRectangularWilsonFreeEnergy_eq_neg_log_expectation,
    cubicalRectangularWilsonExpectation_zero_right]
  norm_num

theorem cubicalRectangularWilsonFreeEnergy_hasAreaBound
    {beta : Real} (hbeta : 0 < beta) :
    HasRectangularAreaBound (cubicalRectangularWilsonFreeEnergy beta) := by
  refine ⟨2 * gaugeDualCoupling beta,
    mul_nonneg (by norm_num) (gaugeDualCoupling_pos hbeta).le, ?_⟩
  intro m n
  by_cases hm : m = 0
  · subst m
    simp
  by_cases hn : n = 0
  · subst n
    simp
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hc : 0 < max m n := hmpos.trans_le (Nat.le_max_left m n)
  have hbound := cubicalXYWilsonFreeEnergy_le_area_mul_dualCoupling
    hmpos hnpos hc (0 : Fin (max m n + 1)) beta hbeta
  calc
    cubicalRectangularWilsonFreeEnergy beta m n ≤
        2 * (m * n : Nat) * gaugeDualCoupling beta := by
      simpa [cubicalRectangularWilsonFreeEnergy] using hbound
    _ = (2 * gaugeDualCoupling beta) * (m : Real) * (n : Real) := by
      push_cast
      ring


theorem cubicalRectangularWilsonFreeEnergy_hasBlockGluing
    {beta : Real} (hbeta : 0 < beta) :
    HasRectangularBlockGluing (cubicalRectangularWilsonFreeEnergy beta) :=
  hasRectangularBlockGluing_of_separatelySubadditive_areaBound
    (cubicalRectangularWilsonFreeEnergy_nonneg hbeta)
    (cubicalRectangularWilsonFreeEnergy_separatelySubadditive hbeta)
    (cubicalRectangularWilsonFreeEnergy_hasAreaBound hbeta)


theorem cubicalSquareWilsonDensity_tendsto_rectangularSurfaceRate_unconditional
    {beta : Real} (hbeta : 0 < beta) :
    Filter.Tendsto (cubicalSquareWilsonDensity beta) Filter.atTop
      (nhds (rectangularSurfaceRate
        (cubicalRectangularWilsonFreeEnergy beta))) :=
  cubicalSquareWilsonDensity_tendsto_rectangularSurfaceRate hbeta
    (cubicalRectangularWilsonFreeEnergy_hasBlockGluing hbeta)


theorem cubicalSquareDisorderDensity_tendsto_rectangularSurfaceRate_unconditional
    {beta : Real} (hbeta : 0 < beta) :
    Filter.Tendsto (cubicalSquareDisorderDensity beta) Filter.atTop
      (nhds (rectangularSurfaceRate
        (cubicalRectangularWilsonFreeEnergy beta))) :=
  cubicalSquareDisorderDensity_tendsto_rectangularSurfaceRate hbeta
    (cubicalRectangularWilsonFreeEnergy_hasBlockGluing hbeta)

end
end StatMech.FrontierA
