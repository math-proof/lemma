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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part29


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem choiceNoHitAtOutputCover_value
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (w : IsingLeapfrogChoiceNoHitAtFamily R t p p' q level) :
    choiceNoHitAtOutputCoverValue R t p p' q level
      (choiceNoHitAtOutputCover R t p p' q level w) = w.1 := by
  classical
  by_cases hs : isingLeapfrogChoiceRun R p w.1.1 = q
  · simp [choiceNoHitAtOutputCover, hs, choiceNoHitAtOutputCoverValue]
  · simp [choiceNoHitAtOutputCover, hs, choiceNoHitAtOutputCoverValue]

theorem choiceNoHitAtOutputCover_injective
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Function.Injective (choiceNoHitAtOutputCover R t p p' q level) := by
  intro a b hab
  apply Subtype.ext
  rw [← choiceNoHitAtOutputCover_value R t p p' q level a,
    ← choiceNoHitAtOutputCover_value R t p p' q level b, hab]

theorem natCard_choiceNoHitAt_le_source_add_mirror
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Nat.card (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level) <=
      Nat.card (IsingSourceChoiceNoHitOutputAtFamily R t p q level) +
        Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R t p p' q level) := by
  calc
    _ <= Nat.card
        (Sum (IsingSourceChoiceNoHitOutputAtFamily R t p q level)
          (IsingMirrorChoiceNoHitOutputAtFamily R t p p' q level)) :=
      Nat.card_le_card_of_injective
        (choiceNoHitAtOutputCover R t p p' q level)
        (choiceNoHitAtOutputCover_injective R t p p' q level)
    _ = _ := Nat.card_sum

theorem choiceNoHitAt_boundary_diffusive_weight_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R)
    (hbottom : rho <= p.2.1) (htop : p.2.1 + rho <= R)
    (hbottom' : rho <= p'.2.1) (htop' : p'.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingLeapfrogChoiceNoHitAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      936 / (rho : Real) ^ 2 := by
  have hcard := natCard_choiceNoHitAt_le_source_add_mirror
    R (rho * rho) p p' q (level : Int)
  have hcardReal :
      (Nat.card (IsingLeapfrogChoiceNoHitAtFamily
        R (rho * rho) p p' q (level : Int)) : Real) <=
      Nat.card (IsingSourceChoiceNoHitOutputAtFamily
        R (rho * rho) p q (level : Int)) +
      Nat.card (IsingMirrorChoiceNoHitOutputAtFamily
        R (rho * rho) p p' q (level : Int)) := by
    exact_mod_cast hcard
  have hsource := sourceChoiceNoHitOutputAt_boundary_diffusive_weight_le
    R level rho p q hstart hρ hleft (by omega) hbottom htop hqBoundary
  have hmirrorBound := mirrorChoiceNoHitOutputAt_boundary_diffusive_weight_le
    R level rho p p' q hstart hmirror hρ hright hbottom' htop' hqBoundary
  calc
    _ <= (Nat.card (IsingSourceChoiceNoHitOutputAtFamily
          R (rho * rho) p q (level : Int)) +
        Nat.card (IsingMirrorChoiceNoHitOutputAtFamily
          R (rho * rho) p p' q (level : Int))) /
          (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = Nat.card (IsingSourceChoiceNoHitOutputAtFamily
          R (rho * rho) p q (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorChoiceNoHitOutputAtFamily
          R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) := by
      rw [add_div]
    _ <= 468 / (rho : Real) ^ 2 + 468 / (rho : Real) ^ 2 :=
      add_le_add hsource hmirrorBound
    _ = 936 / (rho : Real) ^ 2 := by ring

theorem isingLeapfrogStoppedKernel_reflectedStart_boundary_diffusive_abs_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R) (hhalf : R <= 2 * level)
    (hbottom : rho <= p.2.1) (htop : p.2.1 + rho <= R)
    (hbottom' : rho <= p'.2.1) (htop' : p'.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    |isingLeapfrogStoppedKernel R (rho * rho) p q -
        isingLeapfrogStoppedKernel R (rho * rho) p' q| <=
      10296 / (rho : Real) ^ 2 := by
  have hnoHit := choiceNoHitAt_boundary_diffusive_weight_le_of_rightHalf
    R level rho p p' q hstart hmirror hρ hleft hright hbottom htop
      hbottom' htop' hqBoundary
  have hsource := sourceFailureAt_boundary_diffusive_weight_le_of_rightHalf
    R level rho p p' q hstart hmirror hρ hleft (by omega) hright hhalf
      hbottom htop hbottom' htop' hqBoundary
  have hmirrorFailure := mirrorFailureAt_boundary_diffusive_weight_le_of_rightHalf
    R level rho p p' q hstart hmirror hρ hleft hright hhalf hbottom htop
      hbottom' htop' hqBoundary
  apply isingLeapfrogStoppedKernel_reflectedStart_abs_le_of_endpointFailures
    R (rho * rho) p p' q (level : Int) hmirror
  calc
    ((Nat.card (IsingLeapfrogChoiceNoHitAtFamily
          R (rho * rho) p p' q (level : Int)) +
        Nat.card (IsingStoppedCouplingSourceFailureAtFamily
          R (rho * rho) p p' q (level : Int)) +
        Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
          R (rho * rho) p p' q (level : Int)) : Nat) : Real) /
        (4 : Real) ^ (rho * rho) =
      Nat.card (IsingLeapfrogChoiceNoHitAtFamily
          R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) +
      Nat.card (IsingStoppedCouplingSourceFailureAtFamily
          R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) +
      Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
          R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) := by
        push_cast
        ring
    _ <= 936 / (rho : Real) ^ 2 + 936 / (rho : Real) ^ 2 +
        8424 / (rho : Real) ^ 2 :=
      add_le_add (add_le_add hnoHit hsource) hmirrorFailure
    _ = 10296 / (rho : Real) ^ 2 := by ring

theorem sourceFailureOutputAt_horizontal_diffusive_weight_le
    (R level rho : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hleft : rho <= level) (hlevelR : level < R)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
        (level : Int)) / (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  rcases hqHorizontal with hqLeft | hqRight
  · exact sourceFailureOutputAt_left_diffusive_weight_le R level rho p q
      hstart hqLeft hρ hleft
  · rw [sourceFailureOutputAt_right_card_eq_zero R level (rho * rho) p q
      hstart hlevelR hqRight]
    have hnonneg : 0 <= (468 : Real) / (rho : Real) ^ 2 := by positivity
    simpa using hnonneg

theorem mirrorFailureOutputAt_horizontal_diffusive_weight_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
        (level : Int)) / (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  have hlevelR : level <= R := by omega
  have hcard := Nat.card_le_card_of_injective
    (mirrorFailureOutputReflectX R (rho * rho) level p p' q hmirror hlevelR)
    (mirrorFailureOutputReflectX_injective R (rho * rho) level p p' q
      hmirror hlevelR)
  have hcardReal :
      (Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
        (level : Int)) : Real) <=
      Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho)
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        ((R - level : Nat) : Int)) := by exact_mod_cast hcard
  have hp'x : (isingLeapfrogBoxInt p').1 = (level : Int) + 1 := by
    rw [hmirror]
    unfold reflectedEndpoint
    dsimp
    omega
  have hrefStart :
      (isingLeapfrogBoxInt (isingLeapfrogBoxReflectX R p')).1 + 1 =
        (R - level : Nat) := by
    rw [boxInt_reflectX]
    dsimp
    have hcast : ((R - level : Nat) : Int) = (R : Int) - level := by
      rw [Nat.cast_sub hlevelR]
    rw [hcast, hp'x]
    omega
  have hrefHorizontal :
      (isingLeapfrogBoxReflectX R q).1.1 = 0 ∨
        (isingLeapfrogBoxReflectX R q).1.1 = R := by
    rcases hqHorizontal with hq0 | hqR
    · right
      simp [isingLeapfrogBoxReflectX, hq0]
    · left
      simp [isingLeapfrogBoxReflectX, hqR]
  exact (div_le_div_of_nonneg_right hcardReal (by positivity)).trans
    (sourceFailureOutputAt_horizontal_diffusive_weight_le R (R - level) rho
      (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
      hrefStart hρ (by omega) (by omega) hrefHorizontal)

theorem sourceFailureAt_horizontal_diffusive_weight_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level) (hlevelR : level < R)
    (hright : level + rho <= R) (hhalf : R <= 2 * level)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingStoppedCouplingSourceFailureAtFamily R (rho * rho)
        p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <=
      936 / (rho : Real) ^ 2 := by
  have hcard := Nat.card_le_card_of_injective
    (sourceFailureAtAlignedCover_of_rightHalf R level (rho * rho) p p' q
      hstart hmirror hlevelR hhalf)
    (sourceFailureAtAlignedCover_of_rightHalf_injective R level (rho * rho)
      p p' q hstart hmirror hlevelR hhalf)
  rw [Nat.card_sum] at hcard
  have hcardReal :
      (Nat.card (IsingStoppedCouplingSourceFailureAtFamily R (rho * rho)
        p p' q (level : Int)) : Real) <=
      Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
        (level : Int)) +
      Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
        (level : Int)) := by exact_mod_cast hcard
  calc
    _ <= (Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
          (level : Int)) +
        Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
          (level : Int))) / (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
          (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
          (level : Int)) / (4 : Real) ^ (rho * rho) := by rw [add_div]
    _ <= 468 / (rho : Real) ^ 2 + 468 / (rho : Real) ^ 2 := add_le_add
      (sourceFailureOutputAt_horizontal_diffusive_weight_le R level rho p q
        hstart hρ hleft hlevelR hqHorizontal)
      (mirrorFailureOutputAt_horizontal_diffusive_weight_le R level rho p p' q
        hstart hmirror hρ hleft hright hqHorizontal)
    _ = 936 / (rho : Real) ^ 2 := by ring

theorem mirrorFailureAt_horizontal_diffusive_weight_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R) (hhalf : R <= 2 * level)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R (rho * rho)
        p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <=
      1404 / (rho : Real) ^ 2 := by
  have hcard := natCard_mirrorFailureAt_le_aligned_add_residual
    R (rho * rho) p p' q (level : Int)
  have hcardReal :
      (Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R (rho * rho)
        p p' q (level : Int)) : Real) <=
      Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
        (level : Int)) +
      Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
        (level : Int)) +
      Nat.card (IsingMirrorOnlySourceOutputAtFamily R (rho * rho) p p' q
        (level : Int)) := by exact_mod_cast hcard
  have hsource := sourceFailureOutputAt_horizontal_diffusive_weight_le
    R level rho p q hstart hρ hleft (by omega) hqHorizontal
  have hmirrorBound := mirrorFailureOutputAt_horizontal_diffusive_weight_le
    R level rho p p' q hstart hmirror hρ hleft hright hqHorizontal
  have hresidual := mirrorOnlySourceOutputAt_horizontal_diffusive_weight_le
    R level rho p p' q hstart hmirror hρ hright hhalf hqHorizontal
  calc
    _ <= (Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
          (level : Int)) +
        Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
          (level : Int)) +
        Nat.card (IsingMirrorOnlySourceOutputAtFamily R (rho * rho) p p' q
          (level : Int))) / (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
          (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q
          (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorOnlySourceOutputAtFamily R (rho * rho) p p' q
          (level : Int)) / (4 : Real) ^ (rho * rho) := by ring
    _ <= 468 / (rho : Real) ^ 2 + 468 / (rho : Real) ^ 2 +
        468 / (rho : Real) ^ 2 :=
      add_le_add (add_le_add hsource hmirrorBound) hresidual
    _ = 1404 / (rho : Real) ^ 2 := by ring

theorem mirrorChoiceNoHitOutputAt_horizontal_diffusive_weight_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hright : level + rho <= R)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R (rho * rho) p p' q
        (level : Int)) / (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  have hlevelR : level <= R := by omega
  have hcard := Nat.card_le_card_of_injective
    (mirrorNoHitOutputReflectX R (rho * rho) level p p' q hstart hmirror
      hlevelR)
    (mirrorNoHitOutputReflectX_injective R (rho * rho) level p p' q hstart
      hmirror hlevelR)
  have hcardReal :
      (Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R (rho * rho) p p' q
        (level : Int)) : Real) <=
      Nat.card (IsingSourceChoiceNoHitOutputAtFamily R (rho * rho)
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        ((R - level : Nat) : Int)) := by exact_mod_cast hcard
  have hp'x : (isingLeapfrogBoxInt p').1 = (level : Int) + 1 := by
    rw [hmirror]
    unfold reflectedEndpoint
    dsimp
    omega
  have hrefStart :
      (isingLeapfrogBoxInt (isingLeapfrogBoxReflectX R p')).1 + 1 =
        (R - level : Nat) := by
    rw [boxInt_reflectX]
    dsimp
    have hcast : ((R - level : Nat) : Int) = (R : Int) - level := by
      rw [Nat.cast_sub hlevelR]
    rw [hcast, hp'x]
    omega
  have hrefHorizontal :
      (isingLeapfrogBoxReflectX R q).1.1 = 0 ∨
        (isingLeapfrogBoxReflectX R q).1.1 = R := by
    rcases hqHorizontal with hq0 | hqR
    · right; simp [isingLeapfrogBoxReflectX, hq0]
    · left; simp [isingLeapfrogBoxReflectX, hqR]
  exact (div_le_div_of_nonneg_right hcardReal (by positivity)).trans
    (sourceChoiceNoHitOutputAt_horizontal_diffusive_weight_le R (R - level)
      rho (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
      hrefStart hρ (by omega) (Nat.sub_le ..) hrefHorizontal)

theorem choiceNoHitAt_horizontal_diffusive_weight_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingLeapfrogChoiceNoHitAtFamily R (rho * rho) p p' q
        (level : Int)) / (4 : Real) ^ (rho * rho) <=
      936 / (rho : Real) ^ 2 := by
  have hcard := natCard_choiceNoHitAt_le_source_add_mirror
    R (rho * rho) p p' q (level : Int)
  have hcardReal :
      (Nat.card (IsingLeapfrogChoiceNoHitAtFamily R (rho * rho) p p' q
        (level : Int)) : Real) <=
      Nat.card (IsingSourceChoiceNoHitOutputAtFamily R (rho * rho) p q
        (level : Int)) +
      Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R (rho * rho) p p' q
        (level : Int)) := by exact_mod_cast hcard
  calc
    _ <= (Nat.card (IsingSourceChoiceNoHitOutputAtFamily R (rho * rho) p q
          (level : Int)) +
        Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R (rho * rho) p p' q
          (level : Int))) / (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = Nat.card (IsingSourceChoiceNoHitOutputAtFamily R (rho * rho) p q
          (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R (rho * rho) p p' q
          (level : Int)) / (4 : Real) ^ (rho * rho) := by rw [add_div]
    _ <= 468 / (rho : Real) ^ 2 + 468 / (rho : Real) ^ 2 := add_le_add
      (sourceChoiceNoHitOutputAt_horizontal_diffusive_weight_le R level rho
        p q hstart hρ hleft (by omega) hqHorizontal)
      (mirrorChoiceNoHitOutputAt_horizontal_diffusive_weight_le R level rho
        p p' q hstart hmirror hρ hright hqHorizontal)
    _ = 936 / (rho : Real) ^ 2 := by ring

theorem isingLeapfrogStoppedKernel_reflectedStart_horizontalEndpoint_diffusive_abs_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R) (hhalf : R <= 2 * level)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    |isingLeapfrogStoppedKernel R (rho * rho) p q -
        isingLeapfrogStoppedKernel R (rho * rho) p' q| <=
      3276 / (rho : Real) ^ 2 := by
  have hnoHit := choiceNoHitAt_horizontal_diffusive_weight_le_of_rightHalf
    R level rho p p' q hstart hmirror hρ hleft hright hqHorizontal
  have hsource := sourceFailureAt_horizontal_diffusive_weight_le_of_rightHalf
    R level rho p p' q hstart hmirror hρ hleft (by omega) hright hhalf
      hqHorizontal
  have hmirrorFailure :=
    mirrorFailureAt_horizontal_diffusive_weight_le_of_rightHalf
      R level rho p p' q hstart hmirror hρ hleft hright hhalf hqHorizontal
  apply isingLeapfrogStoppedKernel_reflectedStart_abs_le_of_endpointFailures
    R (rho * rho) p p' q (level : Int) hmirror
  calc
    ((Nat.card (IsingLeapfrogChoiceNoHitAtFamily R (rho * rho) p p' q
          (level : Int)) +
        Nat.card (IsingStoppedCouplingSourceFailureAtFamily R (rho * rho)
          p p' q (level : Int)) +
        Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R (rho * rho)
          p p' q (level : Int)) : Nat) : Real) /
        (4 : Real) ^ (rho * rho) =
      Nat.card (IsingLeapfrogChoiceNoHitAtFamily R (rho * rho) p p' q
          (level : Int)) / (4 : Real) ^ (rho * rho) +
      Nat.card (IsingStoppedCouplingSourceFailureAtFamily R (rho * rho)
          p p' q (level : Int)) / (4 : Real) ^ (rho * rho) +
      Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R (rho * rho)
          p p' q (level : Int)) / (4 : Real) ^ (rho * rho) := by
        push_cast
        ring
    _ <= 936 / (rho : Real) ^ 2 + 936 / (rho : Real) ^ 2 +
        1404 / (rho : Real) ^ 2 :=
      add_le_add (add_le_add hnoHit hsource) hmirrorFailure
    _ = 3276 / (rho : Real) ^ 2 := by ring

end
end StatMech.Universality
