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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part9


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem mirrorFailureOutputReflectX_injective
    (R t level : Nat) (p p' q : IsingLeapfrogBox R)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level <= R) :
    Function.Injective
      (mirrorFailureOutputReflectX R t level p p' q hmirror hlevelR) := by
  intro a b hab
  apply Subtype.ext
  exact mirrorFailureReflectX_injective R t level p p' hmirror hlevelR
    (congrArg Subtype.val hab)


theorem mirrorFailureOutputAt_boundary_diffusive_weight_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hlevel : 0 < level)
    (hright : level + rho <= R)
    (hbottom : rho <= p'.2.1) (htop : p'.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
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
  have hrefBottom : rho <= (isingLeapfrogBoxReflectX R p').2.1 := by
    simpa [isingLeapfrogBoxReflectX] using hbottom
  have hrefTop : (isingLeapfrogBoxReflectX R p').2.1 + rho <= R := by
    simpa [isingLeapfrogBoxReflectX] using htop
  have hrefBoundary : isingLeapfrogBoxBoundary R
      (isingLeapfrogBoxReflectX R q) :=
    (isingLeapfrogBoxBoundary_reflectX_iff R q).2 hqBoundary
  calc
    _ <= Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho)
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        ((R - level : Nat) : Int)) / (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ <= 468 / (rho : Real) ^ 2 :=
      sourceFailureOutputAt_boundary_diffusive_weight_le R (R - level) rho
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        hrefStart hρ (by omega) (by omega) hrefBottom hrefTop hrefBoundary

theorem sourceFailure_implies_mirrorFailure_of_rightHalf
    (R level t : Nat) (p p' : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level < R) (hhalf : R <= 2 * level)
    (w : IsingStoppedCouplingSourceFailureFamily R t p (level : Int)) :
    IsingStoppedCouplingMirrorFailure R p p' (level : Int) w.1 := by
  have hstartLt : (isingLeapfrogBoxInt p).1 < (level : Int) := by omega
  rcases sourceFailure_boundary_data R t p (level : Int) hstartLt w with
    ⟨split, j, hsplit, hj, hb, hminimal, hxlt, hrun⟩
  unfold IsingStoppedCouplingMirrorFailure
  refine ⟨split, hsplit, ?_⟩
  intro hmirrorValid
  let w' := isingLeapfrogCouplingChoiceTransform t
    (isingLeapfrogBoxInt p) (level : Int) w.1
  have hbeforeT : split.before.length <= t := by
    have hlen := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
      w.1.2] at hlen
    omega
  have hmirrorValidJ : IsingLeapfrogChoiceExecValid R p' (w'.1.take j) := by
    intro r hr
    have hrj : r < j := by
      dsimp [w'] at hr
      rw [List.length_take] at hr
      omega
    have hw' : (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) (level : Int) w.1).1.length = t :=
      (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) (level : Int) w.1).2
    have hrBefore : r < (List.take split.before.length
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) (level : Int) w.1).1).length := by
      rw [List.length_take, hw']
      omega
    have hv := hmirrorValid r hrBefore
    simpa [w', List.take_take, Nat.min_eq_left hrj.le,
      Nat.min_eq_left (show r <= split.before.length by omega)] using hv
  have hmirrorRun := choiceExecValid_run_boxInt_eq_endpoint R p'
    (w'.1.take j) hmirrorValidJ
  have hbeforeSteps := couplingChoiceTransform_take_steps_of_some t
    (isingLeapfrogBoxInt p) (level : Int) w.1 split hsplit
  have hmirrorSteps : isingLeapfrogChoiceSteps (w'.1.take j) =
      split.reflectPrefix.steps.take j := by
    calc
      _ = (isingLeapfrogChoiceSteps (w'.1.take split.before.length)).take j := by
        simp [isingLeapfrogChoiceSteps, List.map_take, List.take_take,
          Nat.min_eq_left hj.le]
      _ = (split.before.map reflectIncrement).take j := by rw [hbeforeSteps]
      _ = _ := by
        unfold IsingDiagonalWalkHitSplit.reflectPrefix
          IsingDiagonalWalkHitSplit.steps
        rw [List.take_append_of_le_length (by simpa using hj.le)]
  have hsourceSteps : split.steps.take j =
      isingLeapfrogChoiceSteps (w.1.1.take j) := by
    have hs := congrArg (fun path : List (Int × Int) => path.take j)
      (firstHitSplit_steps hsplit)
    simpa [isingLeapfrogChoiceSteps, List.map_take] using hs
  have hmx := congrArg Prod.fst hmirrorRun
  change ((isingLeapfrogChoiceRun R p' (w'.1.take j)).1.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p')
      (isingLeapfrogChoiceSteps (w'.1.take j))).1 at hmx
  rw [hmirror, hmirrorSteps,
    reflectPrefix_endpoint_take_fst_of_le_before split j hj.le,
    hsourceSteps] at hmx
  have hmy := congrArg Prod.snd hmirrorRun
  change ((isingLeapfrogChoiceRun R p' (w'.1.take j)).2.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p')
      (isingLeapfrogChoiceSteps (w'.1.take j))).2 at hmy
  rw [hmirror, hmirrorSteps,
    reflectPrefix_endpoint_take_snd_of_le_before split j hj.le,
    hsourceSteps] at hmy
  have hsx := congrArg Prod.fst hrun
  have hsy := congrArg Prod.snd hrun
  change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
      (isingLeapfrogChoiceSteps (w.1.1.take j))).1 at hsx
  change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).2.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
      (isingLeapfrogChoiceSteps (w.1.1.take j))).2 at hsy
  have hnot := hmirrorValid j (by
    rw [List.length_take]
    have hw' : (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) (level : Int) w.1).1.length = t :=
      (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) (level : Int) w.1).2
    omega)
  have hnot' : ¬ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p' (w'.1.take j)) := by
    simpa [w', List.take_take, Nat.min_eq_left hj.le] using hnot
  apply hnot'
  unfold isingLeapfrogBoxBoundary at hb ⊢
  rcases hb with hx0 | hxR | hy0 | hyR
  · right; left
    have hsourceZero : ((isingLeapfrogChoiceRun R p
        (w.1.1.take j)).1.1 : Int) = 0 := by exact_mod_cast hx0
    have hmirrorX : ((isingLeapfrogChoiceRun R p'
        (w'.1.take j)).1.1 : Int) = 2 * level := by
      rw [hmx, ← hsx, hsourceZero]
      ring
    have hmirrorXNat : (isingLeapfrogChoiceRun R p'
        (w'.1.take j)).1.1 = R := by
      have hle : (isingLeapfrogChoiceRun R p'
          (w'.1.take j)).1.1 <= R := by
        exact Nat.le_of_lt_succ
          (isingLeapfrogChoiceRun R p' (w'.1.take j)).1.2
      have hleInt : (((isingLeapfrogChoiceRun R p'
          (w'.1.take j)).1.1 : Nat) : Int) <= R := by exact_mod_cast hle
      have hhalfInt : (R : Int) <= 2 * level := by exact_mod_cast hhalf
      have heqInt : (((isingLeapfrogChoiceRun R p'
          (w'.1.take j)).1.1 : Nat) : Int) = R := by omega
      exact_mod_cast heqInt
    omega
  · exfalso
    have hsourceRNat : (isingLeapfrogChoiceRun R p
        (w.1.1.take j)).1.1 = R := by omega
    have hsourceR : ((isingLeapfrogChoiceRun R p
        (w.1.1.take j)).1.1 : Int) = R := by exact_mod_cast hsourceRNat
    rw [hsx] at hsourceR
    omega
  · right; right; left
    have hsourceY : ((isingLeapfrogChoiceRun R p
        (w.1.1.take j)).2.1 : Int) = 0 := by exact_mod_cast hy0
    have hmirrorY : ((isingLeapfrogChoiceRun R p'
        (w'.1.take j)).2.1 : Int) = 0 := by rw [hmy, ← hsy, hsourceY]
    exact_mod_cast hmirrorY
  · right; right; right
    have hsourceY : ((isingLeapfrogChoiceRun R p
        (w.1.1.take j)).2.1 : Int) = R := by
      have : (isingLeapfrogChoiceRun R p (w.1.1.take j)).2.1 = R := by omega
      exact_mod_cast this
    have hmirrorY : ((isingLeapfrogChoiceRun R p'
        (w'.1.take j)).2.1 : Int) = R := by rw [hmy, ← hsy, hsourceY]
    have : (isingLeapfrogChoiceRun R p' (w'.1.take j)).2.1 = R := by
      exact_mod_cast hmirrorY
    omega

end
end StatMech.Universality
