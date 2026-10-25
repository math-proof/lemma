/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem horizontalNoHitToNoHitBelow_injective
    (t : Nat) (level : Int) :
    Function.Injective (horizontalNoHitToNoHitBelow t level) := by
  intro a b h
  apply Subtype.ext
  exact congrArg
    (fun w : HorizontalNoHitBelow t (level - 1) level => w.1.1) h


theorem natCard_horizontalNoHit_le_endpointFibers
    (t : Nat) (level : Int) :
    Nat.card (IsingHorizontalNoHitFamily t (level - 1) level) ≤
      Nat.card (VerticalChoicePathFamily t (level - 1) (level - 2)) +
        Nat.card (VerticalChoicePathFamily t (level - 1) (level - 1)) := by
  calc
    _ ≤ Nat.card (HorizontalNoHitBelow t (level - 1) level) :=
      Nat.card_le_card_of_injective (horizontalNoHitToNoHitBelow t level)
        (horizontalNoHitToNoHitBelow_injective t level)
    _ = Nat.card (HorizontalCentralBand t level) :=
      natCard_horizontalNoHitBelow_eq_centralBand t level
    _ = _ := by
      rw [Nat.card_congr (horizontalCentralBandEquivEndpointSum t level),
        Nat.card_sum]


theorem horizontalNoHit_weight_le_sqrt
    (t : Nat) (level : Int) :
    Nat.card (IsingHorizontalNoHitFamily t (level - 1) level) /
        (2 : Real) ^ t ≤ 2 * Real.sqrt (2 / (t + 1 : Real)) := by
  have hcard := natCard_horizontalNoHit_le_endpointFibers t level
  have hden : 0 < (2 : Real) ^ t := by positivity
  have hmass :
      Nat.card (IsingHorizontalNoHitFamily t (level - 1) level) /
          (2 : Real) ^ t ≤
        Nat.card (VerticalChoicePathFamily t (level - 1) (level - 2)) /
            (2 : Real) ^ t +
          Nat.card (VerticalChoicePathFamily t (level - 1) (level - 1)) /
            (2 : Real) ^ t := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hden.le
    exact_mod_cast hcard
  let K₀ := isingLineBinomialKernel t (level - 1) (level - 2)
  let K₁ := isingLineBinomialKernel t (level - 1) (level - 1)
  have hroot0 : 0 ≤ Real.sqrt (2 / (t + 1 : Real)) := Real.sqrt_nonneg _
  have hradicand : 0 ≤ 2 / (t + 1 : Real) := by positivity
  have hK₀0 : 0 ≤ K₀ := isingLineBinomialKernel_nonneg _ _ _
  have hK₁0 : 0 ≤ K₁ := isingLineBinomialKernel_nonneg _ _ _
  have hK₀ : K₀ ≤ Real.sqrt (2 / (t + 1 : Real)) := by
    rw [Real.le_sqrt hK₀0 hradicand]
    exact isingLineBinomialKernel_sq_le t (level - 1) (level - 2)
  have hK₁ : K₁ ≤ Real.sqrt (2 / (t + 1 : Real)) := by
    rw [Real.le_sqrt hK₁0 hradicand]
    exact isingLineBinomialKernel_sq_le t (level - 1) (level - 1)
  calc
    _ ≤ _ := hmass
    _ = K₀ + K₁ := by
      rw [← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div,
        ← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div]
    _ ≤ Real.sqrt (2 / (t + 1 : Real)) +
        Real.sqrt (2 / (t + 1 : Real)) := add_le_add hK₀ hK₁
    _ = 2 * Real.sqrt (2 / (t + 1 : Real)) := by ring


theorem horizontalNoHit_diffusive_weight_le
    (ρ : Nat) (level : Int) (hρ : 0 < ρ) :
    Nat.card (IsingHorizontalNoHitFamily (ρ * ρ) (level - 1) level) /
        (2 : Real) ^ (ρ * ρ) ≤ 4 / (ρ : Real) := by
  have hcard := natCard_horizontalNoHit_le_endpointFibers (ρ * ρ) level
  have hden : 0 < (2 : Real) ^ (ρ * ρ) := by positivity
  have hmass :
      Nat.card (IsingHorizontalNoHitFamily (ρ * ρ) (level - 1) level) /
          (2 : Real) ^ (ρ * ρ) ≤
        (Nat.card (VerticalChoicePathFamily (ρ * ρ) (level - 1)
            (level - 2)) +
          Nat.card (VerticalChoicePathFamily (ρ * ρ) (level - 1)
            (level - 1))) / (2 : Real) ^ (ρ * ρ) := by
    apply div_le_div_of_nonneg_right _ hden.le
    exact_mod_cast hcard
  let K₀ := isingLineBinomialKernel (ρ * ρ) (level - 1) (level - 2)
  let K₁ := isingLineBinomialKernel (ρ * ρ) (level - 1) (level - 1)
  have hK₀0 : 0 ≤ K₀ := isingLineBinomialKernel_nonneg _ _ _
  have hK₁0 : 0 ≤ K₁ := isingLineBinomialKernel_nonneg _ _ _
  have hK₀sq := isingLineBinomialKernel_sq_le
    (ρ * ρ) (level - 1) (level - 2)
  have hK₁sq := isingLineBinomialKernel_sq_le
    (ρ * ρ) (level - 1) (level - 1)
  norm_num [Nat.cast_add, Nat.cast_mul] at hK₀sq hK₁sq
  have hdenρ : 0 < (ρ : Real) ^ 2 + 1 := by positivity
  have hK₀sq' : K₀ ^ 2 * ((ρ : Real) ^ 2 + 1) ≤ 2 := by
    apply (le_div_iff₀ hdenρ).mp
    dsimp [K₀]
    convert hK₀sq using 1 <;> ring
  have hK₁sq' : K₁ ^ 2 * ((ρ : Real) ^ 2 + 1) ≤ 2 := by
    apply (le_div_iff₀ hdenρ).mp
    dsimp [K₁]
    convert hK₁sq using 1 <;> ring
  have hρReal : 0 < (ρ : Real) := by positivity
  have boundKernel (K : Real) (hK0 : 0 ≤ K)
      (hKsq : K ^ 2 * ((ρ : Real) ^ 2 + 1) ≤ 2) :
      K ≤ 2 / (ρ : Real) := by
    apply (le_div_iff₀ hρReal).2
    have hprod0 : 0 ≤ (ρ : Real) * K := mul_nonneg hρReal.le hK0
    have hprodSq : ((ρ : Real) * K) ^ 2 ≤ 2 := by
      nlinarith [sq_nonneg K]
    nlinarith
  have hK₀ := boundKernel K₀ hK₀0 hK₀sq'
  have hK₁ := boundKernel K₁ hK₁0 hK₁sq'
  calc
    _ ≤ _ := hmass
    _ = K₀ + K₁ := by
      rw [add_div]
      rw [← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div,
        ← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div]
    _ ≤ 2 / (ρ : Real) + 2 / (ρ : Real) := add_le_add hK₀ hK₁
    _ = 4 / (ρ : Real) := by ring

theorem lineFreeEndpoint_map_not
    (bs : List Bool) (start level : Int) :
    lineFreeEndpoint (2 * level - start) (bs.map (!·)) =
      2 * level - lineFreeEndpoint start bs := by
  induction bs generalizing start with
  | nil => simp [lineFreeEndpoint]
  | cons b bs ih =>
      cases b with
      | false =>
          simp only [List.map_cons, Bool.not_false, lineFreeEndpoint]
          convert ih (start - 1) using 1 <;> simp <;> ring
      | true =>
          simp only [List.map_cons, Bool.not_true, lineFreeEndpoint]
          convert ih (start + 1) using 1 <;> simp <;> ring

end
end StatMech.Universality
