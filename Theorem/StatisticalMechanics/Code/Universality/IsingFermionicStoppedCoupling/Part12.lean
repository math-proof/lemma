/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part15


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem horizontalEscapeProjection_injective (n t : Nat) :
    Function.Injective (horizontalEscapeProjection n t) := by
  intro a b h
  have hx : a.1.1.map Prod.fst = b.1.1.map Prod.fst :=
    congrArg (fun z => z.1.1) h
  have hy : a.1.1.map Prod.snd = b.1.1.map Prod.snd :=
    congrArg (fun z => z.2.1) h
  apply Subtype.ext
  apply Subtype.ext
  exact prodBits_injective_full hx hy

theorem horizontalEscape_weight_le_inv (n t : Nat) (hn : 0 < n) :
    Nat.card (IsingLeapfrogHorizontalEscapeFamily n t) /
        (4 : Real) ^ t ≤ 1 / (n : Real) := by
  have hcard : Nat.card (IsingLeapfrogHorizontalEscapeFamily n t) ≤
      Nat.card (IsingLineChoicePathFamily n t
        ⟨n - 1, by omega⟩ ⟨0, by omega⟩) * 2 ^ t := by
    calc
      _ ≤ Nat.card (IsingLineChoicePathFamily n t
          ⟨n - 1, by omega⟩ ⟨0, by omega⟩ ×
          {ys : List Bool // ys.length = t}) :=
        Nat.card_le_card_of_injective (horizontalEscapeProjection n t)
          (horizontalEscapeProjection_injective n t)
      _ = _ := by
        rw [Nat.card_prod]
        congr 1
        change Nat.card (List.Vector Bool t) = 2 ^ t
        rw [Nat.card_congr (Equiv.vectorEquivFin Bool t),
          Nat.card_eq_fintype_card, Fintype.card_fun]
        simp
  have hcardReal :
      (Nat.card (IsingLeapfrogHorizontalEscapeFamily n t) : Real) ≤
        Nat.card (IsingLineChoicePathFamily n t
          ⟨n - 1, by omega⟩ ⟨0, by omega⟩) * (2 : Real) ^ t := by
    exact_mod_cast hcard
  have hfour : 0 < (4 : Real) ^ t := by positivity
  have hpow : (4 : Real) ^ t = (2 : Real) ^ t * (2 : Real) ^ t := by
    rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
  calc
    _ ≤ (Nat.card (IsingLineChoicePathFamily n t
          ⟨n - 1, by omega⟩ ⟨0, by omega⟩) * (2 : Real) ^ t) /
          (4 : Real) ^ t := div_le_div_of_nonneg_right hcardReal hfour.le
    _ = Nat.card (IsingLineChoicePathFamily n t
          ⟨n - 1, by omega⟩ ⟨0, by omega⟩) / (2 : Real) ^ t := by
      rw [hpow]
      field_simp
    _ = isingLineStoppedKernel n t ⟨n - 1, by omega⟩ ⟨0, by omega⟩ := by
      rw [isingLineStoppedKernel_eq_natCard_choicePath_div]
    _ ≤ 1 / (n : Real) := isingLineStoppedKernel_left_of_rightNeighbor n t hn


theorem choiceNoHitAll_diffusive_weight_le
    (rho : Nat) (level : Int) (hρ : 0 < rho) :
    Nat.card (IsingLeapfrogChoiceNoHitAll (rho * rho) (level - 1) level) /
        (4 : Real) ^ (rho * rho) ≤ 4 / (rho : Real) := by
  have hcard := natCard_choiceNoHitAll_le_horizontal_mul_pow
    (rho * rho) (level - 1) level
  have hcardReal :
      (Nat.card (IsingLeapfrogChoiceNoHitAll (rho * rho)
          (level - 1) level) : Real) ≤
        Nat.card (IsingHorizontalNoHitFamily (rho * rho)
          (level - 1) level) * (2 : Real) ^ (rho * rho) := by
    exact_mod_cast hcard
  have hfour : 0 < (4 : Real) ^ (rho * rho) := by positivity
  have hpow : (4 : Real) ^ (rho * rho) =
      (2 : Real) ^ (rho * rho) * (2 : Real) ^ (rho * rho) := by
    rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
  calc
    _ ≤ (Nat.card (IsingHorizontalNoHitFamily (rho * rho)
          (level - 1) level) * (2 : Real) ^ (rho * rho)) /
          (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal hfour.le
    _ = Nat.card (IsingHorizontalNoHitFamily (rho * rho)
          (level - 1) level) / (2 : Real) ^ (rho * rho) := by
      rw [hpow]
      field_simp
    _ ≤ 4 / (rho : Real) :=
      horizontalNoHit_diffusive_weight_le rho level hρ


theorem isingLeapfrogChoiceRun_append_full
    (R : Nat) (p : IsingLeapfrogBox R) (a b : List (Bool × Bool)) :
    isingLeapfrogChoiceRun R p (a ++ b) =
      isingLeapfrogChoiceRun R (isingLeapfrogChoiceRun R p a) b := by
  induction a generalizing p with
  | nil => rfl
  | cons x a ih =>
      simp only [List.cons_append, isingLeapfrogChoiceRun]
      exact ih (isingLeapfrogChoiceNext R p x)

theorem isingLeapfrogBoxInt_choiceNext_full
    (R : Nat) (p : IsingLeapfrogBox R) (b : Bool × Bool)
    (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxInt (isingLeapfrogChoiceNext R p b) =
      isingDiagonalWalkNext (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceStep b) := by
  rcases b with ⟨bx, byy⟩
  cases bx <;> cases byy <;>
    simp only [isingLeapfrogChoiceNext, hp, ↓reduceDIte]
  all_goals
    apply Prod.ext <;>
      simp [isingLeapfrogBoxInt, isingLeapfrogChoiceStep,
        isingDiagonalWalkNext, isingLeapfrogSW, isingLeapfrogSE,
        isingLeapfrogNW, isingLeapfrogNE, isingLeapfrogWest,
        isingLeapfrogEast, isingLeapfrogSouth, isingLeapfrogNorth] <;>
      unfold isingLeapfrogBoxBoundary at hp <;> omega


end
end StatMech.Universality
