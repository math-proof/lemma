/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part15


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem horizontalNoHit_diffusive_weight_le_upper
    (ρ : Nat) (level : Int) (hρ : 0 < ρ) :
    Nat.card (IsingHorizontalNoHitFamily (ρ * ρ) (level + 1) level) /
        (2 : Real) ^ (ρ * ρ) ≤ 4 / (ρ : Real) := by
  rw [← Nat.card_congr (horizontalNoHitLowerUpperEquiv (ρ * ρ) level)]
  exact horizontalNoHit_diffusive_weight_le ρ level hρ


theorem killedChoiceNoHitAll_diffusive_weight_le
    (R ρ : Nat) (p : IsingLeapfrogBox R) (level : Int)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level) (hρ : 0 < ρ) :
    Nat.card (IsingLeapfrogKilledChoiceNoHitAll R (ρ * ρ) p level) /
        (4 : Real) ^ (ρ * ρ) ≤ 4 / (ρ : Real) := by
  have hcard := natCard_killedChoiceNoHitAll_le_horizontal_mul_pow
    R (ρ * ρ) p level
  have hcardReal :
      (Nat.card (IsingLeapfrogKilledChoiceNoHitAll R (ρ * ρ) p level) :
          Real) ≤
        Nat.card (IsingHorizontalNoHitFamily (ρ * ρ)
            (isingLeapfrogBoxInt p).1 level) *
          (2 : Real) ^ (ρ * ρ) := by
    exact_mod_cast hcard
  have htwo : 0 < (2 : Real) ^ (ρ * ρ) := by positivity
  have hfour : 0 < (4 : Real) ^ (ρ * ρ) := by positivity
  have hpow : (4 : Real) ^ (ρ * ρ) =
      (2 : Real) ^ (ρ * ρ) * (2 : Real) ^ (ρ * ρ) := by
    rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
  have hreduce :
      Nat.card (IsingLeapfrogKilledChoiceNoHitAll R (ρ * ρ) p level) /
          (4 : Real) ^ (ρ * ρ) ≤
        Nat.card (IsingHorizontalNoHitFamily (ρ * ρ)
            (isingLeapfrogBoxInt p).1 level) /
          (2 : Real) ^ (ρ * ρ) := by
    calc
      _ ≤ (Nat.card (IsingHorizontalNoHitFamily (ρ * ρ)
              (isingLeapfrogBoxInt p).1 level) *
            (2 : Real) ^ (ρ * ρ)) /
          (4 : Real) ^ (ρ * ρ) :=
        div_le_div_of_nonneg_right hcardReal hfour.le
      _ = _ := by
        rw [hpow]
        field_simp
  have hx : (isingLeapfrogBoxInt p).1 = level - 1 := by omega
  calc
    _ ≤ _ := hreduce
    _ ≤ 4 / (ρ : Real) := by
      rw [hx]
      exact horizontalNoHit_diffusive_weight_le ρ level hρ

theorem killedChoiceNoHitAll_diffusive_weight_le_upper
    (R ρ : Nat) (p : IsingLeapfrogBox R) (level : Int)
    (hstart : (isingLeapfrogBoxInt p).1 = level + 1) (hρ : 0 < ρ) :
    Nat.card (IsingLeapfrogKilledChoiceNoHitAll R (ρ * ρ) p level) /
        (4 : Real) ^ (ρ * ρ) ≤ 4 / (ρ : Real) := by
  have hcard := natCard_killedChoiceNoHitAll_le_horizontal_mul_pow
    R (ρ * ρ) p level
  have hcardReal :
      (Nat.card (IsingLeapfrogKilledChoiceNoHitAll R (ρ * ρ) p level) :
          Real) ≤
        Nat.card (IsingHorizontalNoHitFamily (ρ * ρ)
            (isingLeapfrogBoxInt p).1 level) *
          (2 : Real) ^ (ρ * ρ) := by
    exact_mod_cast hcard
  have htwo : 0 < (2 : Real) ^ (ρ * ρ) := by positivity
  have hfour : 0 < (4 : Real) ^ (ρ * ρ) := by positivity
  have hpow : (4 : Real) ^ (ρ * ρ) =
      (2 : Real) ^ (ρ * ρ) * (2 : Real) ^ (ρ * ρ) := by
    rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
  calc
    _ ≤ (Nat.card (IsingHorizontalNoHitFamily (ρ * ρ)
              (isingLeapfrogBoxInt p).1 level) *
            (2 : Real) ^ (ρ * ρ)) /
          (4 : Real) ^ (ρ * ρ) :=
      div_le_div_of_nonneg_right hcardReal hfour.le
    _ = Nat.card (IsingHorizontalNoHitFamily (ρ * ρ)
              (isingLeapfrogBoxInt p).1 level) /
          (2 : Real) ^ (ρ * ρ) := by
      rw [hpow]
      field_simp
    _ ≤ 4 / (ρ : Real) := by
      rw [hstart]
      exact horizontalNoHit_diffusive_weight_le_upper ρ level hρ

end
end StatMech.Universality
