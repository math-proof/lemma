/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem natCard_killedChoicePathFamily_eq_hit_add_noHit
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    Nat.card (IsingLeapfrogKilledChoicePathFamily R t p q) =
      Nat.card (IsingLeapfrogKilledChoiceFirstHitFamily R t p q level) +
        Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) := by
  rw [Nat.card_congr (killedChoicePathFamilyHitNoHitEquiv R t p q level),
    Nat.card_sum]


theorem isingLeapfrogKilledKernel_eq_survivingFirstHit_add_noHit
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    isingLeapfrogKilledKernel R t p q =
      Nat.card (SurvivingFirstHitFamily R (isingLeapfrogBoxInt p) level t
          (isingLeapfrogBoxInt q)) / (4 : Real) ^ t +
        Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) /
          (4 : Real) ^ t := by
  rw [isingLeapfrogKilledKernel_eq_natCard_choicePath_div,
    natCard_killedChoicePathFamily_eq_hit_add_noHit,
    natCard_killedChoiceFirstHitFamily_eq_surviving]
  push_cast
  ring

theorem abs_natCast_sub_eq_natDist (a b : Nat) :
    |(a : Real) - (b : Real)| = Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hab))]
    rw [Nat.dist_eq_sub_of_le hab]
    rw [Nat.cast_sub hab]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hba))]
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba]
    rw [Nat.cast_sub hba]


theorem isingLeapfrogKilledKernel_reflectedStart_abs_le
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    |isingLeapfrogKilledKernel R t p q -
        isingLeapfrogKilledKernel R t p' q| ≤
      (Nat.dist
          (Nat.card (SurvivingFirstHitFamily R (isingLeapfrogBoxInt p)
            level t (isingLeapfrogBoxInt q)))
          (Nat.card (SurvivingFirstHitFamily R
            (reflectedEndpoint level (isingLeapfrogBoxInt p)) level t
            (isingLeapfrogBoxInt q))) : Real) / (4 : Real) ^ t +
        Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) /
          (4 : Real) ^ t +
        Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p' q level) /
          (4 : Real) ^ t := by
  rw [isingLeapfrogKilledKernel_eq_survivingFirstHit_add_noHit,
    isingLeapfrogKilledKernel_eq_survivingFirstHit_add_noHit]
  rw [hmirror]
  let A := Nat.card (SurvivingFirstHitFamily R (isingLeapfrogBoxInt p)
    level t (isingLeapfrogBoxInt q))
  let B := Nat.card (SurvivingFirstHitFamily R
    (reflectedEndpoint level (isingLeapfrogBoxInt p)) level t
    (isingLeapfrogBoxInt q))
  let C := Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level)
  let D := Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p' q level)
  have hden : 0 < (4 : Real) ^ t := by positivity
  calc
    |((A : Real) / 4 ^ t + (C : Real) / 4 ^ t) -
        ((B : Real) / 4 ^ t + (D : Real) / 4 ^ t)| =
        |((A : Real) - B) / 4 ^ t + ((C : Real) - D) / 4 ^ t| := by
      congr 1
      ring
    _ ≤ |((A : Real) - B) / 4 ^ t| +
        |((C : Real) - D) / 4 ^ t| := abs_add_le _ _
    _ = (Nat.dist A B : Real) / 4 ^ t +
        |((C : Real) - D)| / 4 ^ t := by
      simp only [abs_div, abs_of_pos hden]
      rw [abs_natCast_sub_eq_natDist A B]
    _ ≤ (Nat.dist A B : Real) / 4 ^ t +
        (C : Real) / 4 ^ t + (D : Real) / 4 ^ t := by
      have hCD : |(C : Real) - D| ≤ C + D := by
        rw [abs_sub_le_iff]
        have hC0 : (0 : Real) ≤ C := by positivity
        have hD0 : (0 : Real) ≤ D := by positivity
        constructor <;> linarith
      have hdiv := div_le_div_of_nonneg_right hCD hden.le
      calc
        _ ≤ (Nat.dist A B : Real) / 4 ^ t +
            ((C : Real) + D) / 4 ^ t :=
          add_le_add (le_refl _) hdiv
        _ = _ := by ring


theorem killedChoiceNoHitFamily_weight_le_free
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) /
        (4 : Real) ^ t ≤
      2 / (t + 1 : Real) := by
  have hcard :
      Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) ≤
        Nat.card (IsingLeapfrogKilledChoicePathFamily R t p q) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hcardReal :
      (Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) :
        Real) ≤
      Nat.card (IsingLeapfrogKilledChoicePathFamily R t p q) := by
    exact_mod_cast hcard
  calc
    Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) /
        (4 : Real) ^ t ≤
      Nat.card (IsingLeapfrogKilledChoicePathFamily R t p q) /
        (4 : Real) ^ t :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = isingLeapfrogKilledKernel R t p q := by
      rw [isingLeapfrogKilledKernel_eq_natCard_choicePath_div]
    _ ≤ 2 / (t + 1 : Real) :=
      isingLeapfrogKilledKernel_le R t p q


theorem isingLeapfrogKilledKernel_reflectedStart_diffusive_abs_le
    (R level ρ : Nat) (p p' q : IsingLeapfrogBox R)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < ρ) (hleft : ρ + 1 ≤ level)
    (hright : level + 1 + ρ ≤ R) :
    |isingLeapfrogKilledKernel R (ρ * ρ) p q -
        isingLeapfrogKilledKernel R (ρ * ρ) p' q| ≤
      8 / (ρ : Real) ^ 2 := by
  have hdecomp := isingLeapfrogKilledKernel_reflectedStart_abs_le R
    (ρ * ρ) p p' q (level : Int) hmirror
  have hhit := survivingFirstHitFamily_diffusive_weight_dist_le R level ρ
    (isingLeapfrogBoxInt p) (isingLeapfrogBoxInt q) hstart hρ hleft hright
  have hno := killedChoiceNoHitFamily_weight_le_free R (ρ * ρ) p q
    (level : Int)
  have hno' := killedChoiceNoHitFamily_weight_le_free R (ρ * ρ) p' q
    (level : Int)
  norm_num [Nat.cast_add, Nat.cast_mul] at hno hno'
  have hρsq : 0 < (ρ : Real) ^ 2 := by positivity
  have hnoBound :
      Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R (ρ * ρ) p q
          (level : Int)) / (4 : Real) ^ (ρ * ρ) ≤
        2 / (ρ : Real) ^ 2 := by
    refine le_trans hno (div_le_div_of_nonneg_left (by norm_num) hρsq ?_)
    nlinarith
  have hnoBound' :
      Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R (ρ * ρ) p' q
          (level : Int)) / (4 : Real) ^ (ρ * ρ) ≤
        2 / (ρ : Real) ^ 2 := by
    refine le_trans hno' (div_le_div_of_nonneg_left (by norm_num) hρsq ?_)
    nlinarith
  calc
    _ ≤ _ := hdecomp
    _ ≤ 4 / (ρ : Real) ^ 2 + 2 / (ρ : Real) ^ 2 +
        2 / (ρ : Real) ^ 2 := add_le_add (add_le_add hhit hnoBound) hnoBound'
    _ = 8 / (ρ : Real) ^ 2 := by ring


theorem firstHitSplit_none_endpoint_fst_ne
    {start : Int × Int} {level : Int} {path : List (Int × Int)}
    (hnone : isingDiagonalWalkFirstHitSplit? start level path = none) :
    ∀ k, k ≤ path.length →
      (isingDiagonalWalkEndpoint start (path.take k)).1 ≠ level := by
  induction path generalizing start with
  | nil =>
      intro k hk
      have hk0 : k = 0 := by simp_all
      subst k
      by_cases hs : start.1 = level
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at hnone
      · simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
          using hs
  | cons d path ih =>
      by_cases hs : start.1 = level
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at hnone
      · have htail : isingDiagonalWalkFirstHitSplit?
            (isingDiagonalWalkNext start d) level path = none := by
          cases hrec : isingDiagonalWalkFirstHitSplit?
              (isingDiagonalWalkNext start d) level path with
          | none => rfl
          | some split =>
              simp [isingDiagonalWalkFirstHitSplit?, hs, hrec] at hnone
        intro k hk
        cases k with
        | zero =>
            simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
              using hs
        | succ k =>
            have hkTail : k ≤ path.length := by simpa using hk
            have hne := ih htail k hkTail
            simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
              isingDiagonalWalkDisplacement, add_assoc] using hne

theorem lineFreeEndpoint_choiceHorizontal
    (bs : List (Bool × Bool)) (start : Int × Int) :
    lineFreeEndpoint start.1 (bs.map Prod.fst) =
      (isingDiagonalWalkEndpoint start
        (isingLeapfrogChoiceSteps bs)).1 := by
  induction bs generalizing start with
  | nil =>
      simp [lineFreeEndpoint,
        isingLeapfrogChoiceSteps, isingDiagonalWalkEndpoint,
        isingDiagonalWalkDisplacement]
  | cons b bs ih =>
      have hih := ih (isingDiagonalWalkNext start
        (isingLeapfrogChoiceStep b))
      rcases b with ⟨bx, byy⟩
      cases bx <;> cases byy <;>
        simp [lineFreeEndpoint,
          isingLeapfrogChoiceSteps, isingLeapfrogChoiceStep,
          isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
          isingDiagonalWalkDisplacement, add_assoc] at hih ⊢ <;>
        linarith


end
end StatMech.Universality
