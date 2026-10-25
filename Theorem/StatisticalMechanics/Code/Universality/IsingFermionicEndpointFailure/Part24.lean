/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part27


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem sourceNoHitVerticalCover_value
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 ∨ q.2.1 = R)
    (w : IsingSourceChoiceNoHitOutputAtFamily R t p q (level : Int)) :
    tailDependentEndpointRaceValue R t rho p q (level : Int)
      (sourceNoHitVerticalCover R level rho t p q hstart hρ hbottom htop
        hqVertical w) = w.1 := by
  exact Classical.choose_spec (exists_sourceNoHitVerticalCover R level rho t
    p q hstart hρ hbottom htop hqVertical w)

theorem sourceNoHitVerticalCover_injective
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 ∨ q.2.1 = R) :
    Function.Injective
      (sourceNoHitVerticalCover R level rho t p q hstart hρ hbottom htop
        hqVertical) := by
  intro a b hab
  apply Subtype.ext
  rw [← sourceNoHitVerticalCover_value R level rho t p q hstart hρ hbottom
      htop hqVertical a,
    ← sourceNoHitVerticalCover_value R level rho t p q hstart hρ hbottom
      htop hqVertical b, hab]

theorem sourceChoiceNoHitOutputAt_vertical_diffusive_weight_le
    (R level rho : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 ∨ q.2.1 = R) :
    Nat.card (IsingSourceChoiceNoHitOutputAtFamily
        R (rho * rho) p q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      24 / (rho : Real) ^ 2 := by
  have hcard := Nat.card_le_card_of_injective
    (sourceNoHitVerticalCover R level rho (rho * rho) p q hstart hρ hbottom
      htop hqVertical)
    (sourceNoHitVerticalCover_injective R level rho (rho * rho) p q hstart hρ
      hbottom htop hqVertical)
  have hcardReal :
      (Nat.card (IsingSourceChoiceNoHitOutputAtFamily
        R (rho * rho) p q (level : Int)) : Real) <=
      Nat.card (IsingTailDependentEndpointRaceFamily rho (rho * rho)
        (level : Int) (sourceEndpointRaceTarget R (rho * rho) rho p q)) := by
    exact_mod_cast hcard
  exact (div_le_div_of_nonneg_right hcardReal (by positivity)).trans
    (tailDependentEndpointRace_diffusive_weight_le rho rho (level : Int)
      (sourceEndpointRaceTarget R (rho * rho) rho p q) hρ (le_refl _))

theorem sourceChoiceNoHitOutputAt_boundary_diffusive_weight_le
    (R level rho : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hleft : rho <= level) (hlevelR : level <= R)
    (hbottom : rho <= p.2.1) (htop : p.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingSourceChoiceNoHitOutputAtFamily
        R (rho * rho) p q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  unfold isingLeapfrogBoxBoundary at hqBoundary
  rcases hqBoundary with hqLeft | hqRight | hqBottom | hqTop
  · exact sourceChoiceNoHitOutputAt_horizontal_diffusive_weight_le
      R level rho p q hstart hρ hleft hlevelR (Or.inl hqLeft)
  · exact sourceChoiceNoHitOutputAt_horizontal_diffusive_weight_le
      R level rho p q hstart hρ hleft hlevelR (Or.inr (by omega))
  · exact (sourceChoiceNoHitOutputAt_vertical_diffusive_weight_le
      R level rho p q hstart hρ hbottom htop (Or.inl hqBottom)).trans (by
        apply div_le_div_of_nonneg_right (by norm_num)
        positivity)
  · exact (sourceChoiceNoHitOutputAt_vertical_diffusive_weight_le
      R level rho p q hstart hρ hbottom htop (Or.inr (by omega))).trans (by
        apply div_le_div_of_nonneg_right (by norm_num)
        positivity)

theorem firstHitSplit_eq_none_of_choice_noHit
    {start : Int × Int} {level : Int} {path : List (Int × Int)}
    (havoid : forall k, k <= path.length ->
      (isingDiagonalWalkEndpoint start (path.take k)).1 ≠ level) :
    isingDiagonalWalkFirstHitSplit? start level path = none := by
  cases hsplit : isingDiagonalWalkFirstHitSplit? start level path with
  | none => rfl
  | some split =>
      exfalso
      have hsteps := firstHitSplit_steps hsplit
      have hk : split.before.length <= path.length := by
        rw [← hsteps]
        simp [IsingDiagonalWalkHitSplit.steps]
      exact (havoid split.before.length hk) (by
        have htake : path.take split.before.length = split.before := by
          rw [← hsteps]
          simp [IsingDiagonalWalkHitSplit.steps]
        rw [htake]
        exact split.hit)

theorem flipX_encode_reflected_choiceSteps (bs : List (Bool × Bool)) :
    isingLeapfrogFlipXChoices
        (isingLeapfrogEncodeSteps
          ((isingLeapfrogChoiceSteps bs).map reflectIncrement)) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change
        ((!(isingLeapfrogEncodeStep
            (reflectIncrement (isingLeapfrogChoiceStep b))).1,
          (isingLeapfrogEncodeStep
            (reflectIncrement (isingLeapfrogChoiceStep b))).2) ::
          isingLeapfrogFlipXChoices
            (isingLeapfrogEncodeSteps
              ((isingLeapfrogChoiceSteps bs).map reflectIncrement))) = b :: bs
      rw [ih]
      rcases b with ⟨bx, byy⟩
      cases bx <;> cases byy <;>
        simp [isingLeapfrogChoiceStep, isingLeapfrogEncodeStep,
          reflectIncrement]

theorem couplingChoiceTransform_flipX_eq_of_noHit
    (t : Nat) (start : Int × Int) (level : Int)
    (w : IsingLeapfrogChoiceStringFamily t)
    (havoid : forall k, k <= t -> lineFreeEndpoint start.1
      ((w.1.map Prod.fst).take k) ≠ level) :
    isingLeapfrogFlipXChoices
        (isingLeapfrogCouplingChoiceTransform t start level w).1 = w.1 := by
  have hnone : isingDiagonalWalkFirstHitSplit? start level
      (isingLeapfrogChoiceSteps w.1) = none := by
    apply firstHitSplit_eq_none_of_choice_noHit
    intro k hk
    have hkt : k <= t := by
      simpa [isingLeapfrogChoiceSteps, w.2] using hk
    have hw := havoid k hkt
    rw [show (isingLeapfrogChoiceSteps w.1).take k =
        isingLeapfrogChoiceSteps (w.1.take k) by
          simp [isingLeapfrogChoiceSteps, List.map_take]]
    rw [← lineFreeEndpoint_choiceHorizontal_full]
    simpa [List.map_take] using hw
  unfold isingLeapfrogCouplingChoiceTransform
  dsimp only
  unfold isingDiagonalWalkCouplingReflectSteps
  rw [hnone]
  exact flipX_encode_reflected_choiceSteps w.1

end
end StatMech.Universality
