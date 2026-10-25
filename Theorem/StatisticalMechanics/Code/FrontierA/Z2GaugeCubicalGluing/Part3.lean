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
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part2
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

theorem cubicalPlaquetteIncidence_chart {a b c A B C : Nat}
    (ox oy oz : Nat) (hx : ox + a ≤ A) (hy : oy + b ≤ B)
    (hz : oz + c ≤ C) (p : CubicalPlaquette a b c) :
    cubicalPlaquetteIncidence
        (cubicalPlaquetteChart ox oy oz hx hy hz p) =
      (cubicalPlaquetteIncidence p).map
        (cubicalEdgeChart ox oy oz hx hy hz) := by
  cases p <;>
    simp [cubicalPlaquetteIncidence, cubicalPlaquetteChart,
      cubicalEdgeChart]


theorem cubicalXYWilsonExpectation_le_chart {a b c A B C : Nat}
    (ox oy oz : Nat) (hx : ox + a ≤ A) (hy : oy + b ≤ B)
    (hz : oz + c ≤ C) {beta : Real} (hbeta : 0 ≤ beta)
    (z : Fin (c + 1)) :
    gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette a b c => beta) (cubicalXYLoop z) ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette A B C => beta)
        ((cubicalXYLoop z).map (cubicalEdgeChart ox oy oz hx hy hz)) := by
  let eEmb := cubicalEdgeChart ox oy oz hx hy hz
  let pEmb := cubicalPlaquetteChart ox oy oz hx hy hz
  let Ksmall := fun _ : CubicalPlaquette a b c => beta
  have hzero : ∀ p, 0 ≤ extendGaugeCoupling pEmb Ksmall p := by
    intro p
    unfold extendGaugeCoupling
    cases (embeddingSplitEquiv pEmb).symm p with
    | inl q => exact hbeta
    | inr q => exact le_rfl
  have hle : ∀ p, extendGaugeCoupling pEmb Ksmall p ≤ beta := by
    intro p
    unfold extendGaugeCoupling
    cases (embeddingSplitEquiv pEmb).symm p with
    | inl q => exact le_rfl
    | inr q => exact hbeta
  calc
    gaugeWilsonExpectation cubicalPlaquetteIncidence Ksmall (cubicalXYLoop z) =
        gaugeWilsonExpectation cubicalPlaquetteIncidence
          (extendGaugeCoupling pEmb Ksmall) ((cubicalXYLoop z).map eEmb) :=
      (gaugeWilsonExpectation_extendGaugeCoupling
        cubicalPlaquetteIncidence cubicalPlaquetteIncidence eEmb pEmb
        (cubicalPlaquetteIncidence_chart ox oy oz hx hy hz) Ksmall
        (cubicalXYLoop z)).symm
    _ ≤ gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette A B C => beta)
          ((cubicalXYLoop z).map eEmb) :=
      gaugeWilsonExpectation_mono_coupling cubicalPlaquetteIncidence
        (extendGaugeCoupling pEmb Ksmall) (fun _ => beta) hzero hle _

theorem cubicalXYSheet_horizontal_union (m l n c₁ c₂ C : Nat)
    (hc₁ : c₁ ≤ C) (hc₂ : c₂ ≤ C) :
    (cubicalXYSheet (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map
          (cubicalPlaquetteChart 0 0 0 (by omega) (by omega) (by omega)) ∪
      (cubicalXYSheet (a := l) (b := n) (c := c₂) (0 : Fin (c₂ + 1))).map
          (cubicalPlaquetteChart m 0 0 (by omega) (by omega) (by omega)) =
        cubicalXYSheet (a := m + l) (b := n) (c := C) (0 : Fin (C + 1)) := by
  ext p
  cases p with
  | xy i j k =>
      simp [cubicalXYSheet, cubicalPlaquetteChart, finOffsetEmbedding]
      constructor
      · rintro (⟨_, _, hk⟩ | ⟨_, _, hk⟩) <;> exact hk
      · intro hk
        by_cases hi : i.val < m
        · left
          refine ⟨⟨⟨i.val, hi⟩, ?_⟩, ⟨⟨j.val, j.isLt⟩, ?_⟩, hk⟩
          · apply Fin.ext
            simp [finOffsetEmbedding]
          · apply Fin.ext
            simp [finOffsetEmbedding]
        · right
          have hil : i.val - m < l := by omega
          refine ⟨⟨⟨i.val - m, hil⟩, ?_⟩, ⟨⟨j.val, j.isLt⟩, ?_⟩, hk⟩
          · apply Fin.ext
            simp [finOffsetEmbedding]
            omega
          · apply Fin.ext
            simp [finOffsetEmbedding]
  | xz i j k => simp [cubicalXYSheet, cubicalPlaquetteChart]
  | yz i j k => simp [cubicalXYSheet, cubicalPlaquetteChart]

theorem cubicalXYSheet_horizontal_disjoint (m l n c₁ c₂ C : Nat)
    (hc₁ : c₁ ≤ C) (hc₂ : c₂ ≤ C) :
    Disjoint
      ((cubicalXYSheet (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map
        (cubicalPlaquetteChart (A := m + l) (B := n) (C := C)
          0 0 0 (by omega) (by omega) (by omega)))
      ((cubicalXYSheet (a := l) (b := n) (c := c₂) (0 : Fin (c₂ + 1))).map
        (cubicalPlaquetteChart (A := m + l) (B := n) (C := C)
          m 0 0 (by omega) (by omega) (by omega))) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  cases p with
  | xy i j k =>
      simp [cubicalXYSheet, cubicalPlaquetteChart, finOffsetEmbedding] at hp₁ hp₂
      obtain ⟨⟨x₁, _⟩, hx₁⟩ := hp₁.1
      obtain ⟨⟨x₂, _⟩, hx₂⟩ := hp₂.1
      have hv₁ := congrArg Fin.val hx₁
      have hv₂ := congrArg Fin.val hx₂
      simp at hv₁ hv₂
      omega
  | xz i j k => simp [cubicalXYSheet, cubicalPlaquetteChart] at hp₁
  | yz i j k => simp [cubicalXYSheet, cubicalPlaquetteChart] at hp₁

theorem cubicalXYLoop_horizontal_symmDiff (m l n c₁ c₂ C : Nat)
    (hc₁ : c₁ ≤ C) (hc₂ : c₂ ≤ C) :
    (cubicalXYLoop (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map
          (cubicalEdgeChart (A := m + l) (B := n) (C := C)
            0 0 0 (by omega) (by omega) (by omega)) ∆
      (cubicalXYLoop (a := l) (b := n) (c := c₂) (0 : Fin (c₂ + 1))).map
          (cubicalEdgeChart (A := m + l) (B := n) (C := C)
            m 0 0 (by omega) (by omega) (by omega)) =
        cubicalXYLoop (a := m + l) (b := n) (c := C) (0 : Fin (C + 1)) := by
  let P₁ := cubicalPlaquetteChart (a := m) (b := n) (c := c₁)
    (A := m + l) (B := n) (C := C)
    0 0 0 (by omega) (by omega) (by omega)
  let P₂ := cubicalPlaquetteChart (a := l) (b := n) (c := c₂)
    (A := m + l) (B := n) (C := C)
    m 0 0 (by omega) (by omega) (by omega)
  let E₁ := cubicalEdgeChart (a := m) (b := n) (c := c₁)
    (A := m + l) (B := n) (C := C)
    0 0 0 (by omega) (by omega) (by omega)
  let E₂ := cubicalEdgeChart (a := l) (b := n) (c := c₂)
    (A := m + l) (B := n) (C := C)
    m 0 0 (by omega) (by omega) (by omega)
  let S₁ := (cubicalXYSheet (a := m) (b := n) (c := c₁)
    (0 : Fin (c₁ + 1))).map P₁
  let S₂ := (cubicalXYSheet (a := l) (b := n) (c := c₂)
    (0 : Fin (c₂ + 1))).map P₂
  change (gaugeSurfaceBoundary cubicalPlaquetteIncidence
      (cubicalXYSheet (0 : Fin (c₁ + 1)))).map E₁ ∆
    (gaugeSurfaceBoundary cubicalPlaquetteIncidence
      (cubicalXYSheet (0 : Fin (c₂ + 1)))).map E₂ = _
  rw [← gaugeSurfaceBoundary_map cubicalPlaquetteIncidence
      cubicalPlaquetteIncidence E₁ P₁
      (cubicalPlaquetteIncidence_chart 0 0 0 _ _ _),
    ← gaugeSurfaceBoundary_map cubicalPlaquetteIncidence
      cubicalPlaquetteIncidence E₂ P₂
      (cubicalPlaquetteIncidence_chart m 0 0 _ _ _)]
  change gaugeSurfaceBoundary cubicalPlaquetteIncidence S₁ ∆
    gaugeSurfaceBoundary cubicalPlaquetteIncidence S₂ = _
  rw [← gaugeSurfaceBoundary_union_of_disjoint cubicalPlaquetteIncidence
    (cubicalXYSheet_horizontal_disjoint m l n c₁ c₂ C hc₁ hc₂)]
  have hunion : S₁ ∪ S₂ =
      cubicalXYSheet (a := m + l) (b := n) (c := C) (0 : Fin (C + 1)) :=
    cubicalXYSheet_horizontal_union m l n c₁ c₂ C hc₁ hc₂
  rw [hunion]
  rfl

theorem cubicalXYSheet_vertical_union (m n k c₁ c₂ C : Nat)
    (hc₁ : c₁ ≤ C) (hc₂ : c₂ ≤ C) :
    (cubicalXYSheet (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map
          (cubicalPlaquetteChart 0 0 0 (by omega) (by omega) (by omega)) ∪
      (cubicalXYSheet (a := m) (b := k) (c := c₂) (0 : Fin (c₂ + 1))).map
          (cubicalPlaquetteChart 0 n 0 (by omega) (by omega) (by omega)) =
        cubicalXYSheet (a := m) (b := n + k) (c := C) (0 : Fin (C + 1)) := by
  ext p
  cases p with
  | xy i j z =>
      simp [cubicalXYSheet, cubicalPlaquetteChart, finOffsetEmbedding]
      constructor
      · rintro (⟨_, _, hz⟩ | ⟨_, _, hz⟩) <;> exact hz
      · intro hz
        by_cases hj : j.val < n
        · left
          refine ⟨⟨⟨i.val, i.isLt⟩, ?_⟩, ⟨⟨j.val, hj⟩, ?_⟩, hz⟩
          · apply Fin.ext
            simp
          · apply Fin.ext
            simp
        · right
          have hjk : j.val - n < k := by omega
          refine ⟨⟨⟨i.val, i.isLt⟩, ?_⟩, ⟨⟨j.val - n, hjk⟩, ?_⟩, hz⟩
          · apply Fin.ext
            simp
          · apply Fin.ext
            simp
            omega
  | xz i j z => simp [cubicalXYSheet, cubicalPlaquetteChart]
  | yz i j z => simp [cubicalXYSheet, cubicalPlaquetteChart]

theorem cubicalXYSheet_vertical_disjoint (m n k c₁ c₂ C : Nat)
    (hc₁ : c₁ ≤ C) (hc₂ : c₂ ≤ C) :
    Disjoint
      ((cubicalXYSheet (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map
        (cubicalPlaquetteChart (A := m) (B := n + k) (C := C)
          0 0 0 (by omega) (by omega) (by omega)))
      ((cubicalXYSheet (a := m) (b := k) (c := c₂) (0 : Fin (c₂ + 1))).map
        (cubicalPlaquetteChart (A := m) (B := n + k) (C := C)
          0 n 0 (by omega) (by omega) (by omega))) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  cases p with
  | xy i j z =>
      simp [cubicalXYSheet, cubicalPlaquetteChart, finOffsetEmbedding] at hp₁ hp₂
      obtain ⟨⟨y₁, _⟩, hy₁⟩ := hp₁.2.1
      obtain ⟨⟨y₂, _⟩, hy₂⟩ := hp₂.2.1
      have hv₁ := congrArg Fin.val hy₁
      have hv₂ := congrArg Fin.val hy₂
      simp at hv₁ hv₂
      omega
  | xz i j z => simp [cubicalXYSheet, cubicalPlaquetteChart] at hp₁
  | yz i j z => simp [cubicalXYSheet, cubicalPlaquetteChart] at hp₁

theorem cubicalXYLoop_vertical_symmDiff (m n k c₁ c₂ C : Nat)
    (hc₁ : c₁ ≤ C) (hc₂ : c₂ ≤ C) :
    (cubicalXYLoop (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map
          (cubicalEdgeChart (A := m) (B := n + k) (C := C)
            0 0 0 (by omega) (by omega) (by omega)) ∆
      (cubicalXYLoop (a := m) (b := k) (c := c₂) (0 : Fin (c₂ + 1))).map
          (cubicalEdgeChart (A := m) (B := n + k) (C := C)
            0 n 0 (by omega) (by omega) (by omega)) =
        cubicalXYLoop (a := m) (b := n + k) (c := C) (0 : Fin (C + 1)) := by
  let P₁ := cubicalPlaquetteChart (a := m) (b := n) (c := c₁)
    (A := m) (B := n + k) (C := C) 0 0 0 (by omega) (by omega) (by omega)
  let P₂ := cubicalPlaquetteChart (a := m) (b := k) (c := c₂)
    (A := m) (B := n + k) (C := C) 0 n 0 (by omega) (by omega) (by omega)
  let E₁ := cubicalEdgeChart (a := m) (b := n) (c := c₁)
    (A := m) (B := n + k) (C := C) 0 0 0 (by omega) (by omega) (by omega)
  let E₂ := cubicalEdgeChart (a := m) (b := k) (c := c₂)
    (A := m) (B := n + k) (C := C) 0 n 0 (by omega) (by omega) (by omega)
  let S₁ := (cubicalXYSheet (a := m) (b := n) (c := c₁)
    (0 : Fin (c₁ + 1))).map P₁
  let S₂ := (cubicalXYSheet (a := m) (b := k) (c := c₂)
    (0 : Fin (c₂ + 1))).map P₂
  change (gaugeSurfaceBoundary cubicalPlaquetteIncidence
      (cubicalXYSheet (0 : Fin (c₁ + 1)))).map E₁ ∆
    (gaugeSurfaceBoundary cubicalPlaquetteIncidence
      (cubicalXYSheet (0 : Fin (c₂ + 1)))).map E₂ = _
  rw [← gaugeSurfaceBoundary_map cubicalPlaquetteIncidence
      cubicalPlaquetteIncidence E₁ P₁
      (cubicalPlaquetteIncidence_chart 0 0 0 _ _ _),
    ← gaugeSurfaceBoundary_map cubicalPlaquetteIncidence
      cubicalPlaquetteIncidence E₂ P₂
      (cubicalPlaquetteIncidence_chart 0 n 0 _ _ _)]
  change gaugeSurfaceBoundary cubicalPlaquetteIncidence S₁ ∆
    gaugeSurfaceBoundary cubicalPlaquetteIncidence S₂ = _
  rw [← gaugeSurfaceBoundary_union_of_disjoint cubicalPlaquetteIncidence
    (cubicalXYSheet_vertical_disjoint m n k c₁ c₂ C hc₁ hc₂)]
  have hunion : S₁ ∪ S₂ =
      cubicalXYSheet (a := m) (b := n + k) (c := C) (0 : Fin (C + 1)) :=
    cubicalXYSheet_vertical_union m n k c₁ c₂ C hc₁ hc₂
  rw [hunion]
  rfl


end
end StatMech.FrontierA
