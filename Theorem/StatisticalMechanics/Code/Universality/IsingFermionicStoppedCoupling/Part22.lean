/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part26


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem mirrorFailureReflectX_injective
    (R t level : Nat) (p p' : IsingLeapfrogBox R)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level ≤ R) :
    Function.Injective
      (mirrorFailureReflectX R t level p p' hmirror hlevelR) :=
  (sourceFailureReflectX_injective R t p' level hlevelR).comp
    (mirrorFailureToSource_injective R t p p' (level : Int) hmirror)

theorem mirrorFailure_diffusive_weight_le
    (R level rho : Nat) (p p' : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hlevel : 0 < level)
    (hright : level + rho ≤ R)
    (hbottom : rho ≤ p'.2.1) (htop : p'.2.1 + rho ≤ R) :
    Nat.card (IsingStoppedCouplingMirrorFailureFamily R (rho * rho) p p'
        (level : Int)) / (4 : Real) ^ (rho * rho) ≤ 17 / (rho : Real) := by
  have hlevelR : level ≤ R := by omega
  have hcard : Nat.card (IsingStoppedCouplingMirrorFailureFamily R
      (rho * rho) p p' (level : Int)) ≤
      Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho)
        (isingLeapfrogBoxReflectX R p') ((R - level : Nat) : Int)) :=
    Nat.card_le_card_of_injective
      (mirrorFailureReflectX R (rho * rho) level p p' hmirror hlevelR)
      (mirrorFailureReflectX_injective R (rho * rho) level p p' hmirror hlevelR)
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
  have hrefLeft : rho ≤ R - level := by omega
  have hrefRight : R - level < R := by omega
  have hrefBottom : rho ≤ (isingLeapfrogBoxReflectX R p').2.1 := by
    simpa [isingLeapfrogBoxReflectX] using hbottom
  have hrefTop : (isingLeapfrogBoxReflectX R p').2.1 + rho ≤ R := by
    simpa [isingLeapfrogBoxReflectX] using htop
  have hsource := sourceFailure_diffusive_weight_le R (R - level) rho
    (isingLeapfrogBoxReflectX R p') hrefStart hρ hrefLeft hrefRight
      hrefBottom hrefTop
  have hcardReal :
      (Nat.card (IsingStoppedCouplingMirrorFailureFamily R (rho * rho) p p'
        (level : Int)) : Real) ≤
      Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho)
        (isingLeapfrogBoxReflectX R p') ((R - level : Nat) : Int)) := by
    exact_mod_cast hcard
  exact le_trans (div_le_div_of_nonneg_right hcardReal (by positivity)) hsource

theorem stoppedCouplingBad_diffusive_weight_le
    (R level rho : Nat) (p p' : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho ≤ level) (hright : level + rho ≤ R)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R) :
    Nat.card (IsingLeapfrogStoppedCouplingBadFamily R (rho * rho) p p'
        (level : Int)) / (4 : Real) ^ (rho * rho) ≤ 38 / (rho : Real) := by
  have hcover := natCard_stoppedCouplingBad_le_noHit_add_failures R
    (rho * rho) p p' (level : Int) hmirror
  have hcoverReal :
      (Nat.card (IsingLeapfrogStoppedCouplingBadFamily R (rho * rho) p p'
        (level : Int)) : Real) ≤
      Nat.card (IsingLeapfrogChoiceNoHitAll (rho * rho)
        (isingLeapfrogBoxInt p).1 (level : Int)) +
      Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho) p
        (level : Int)) +
      Nat.card (IsingStoppedCouplingMirrorFailureFamily R (rho * rho) p p'
        (level : Int)) := by exact_mod_cast hcover
  have hnohit : Nat.card (IsingLeapfrogChoiceNoHitAll (rho * rho)
      (isingLeapfrogBoxInt p).1 (level : Int)) /
        (4 : Real) ^ (rho * rho) ≤ 4 / (rho : Real) := by
    have hx : (isingLeapfrogBoxInt p).1 = (level : Int) - 1 := by omega
    rw [hx]
    exact choiceNoHitAll_diffusive_weight_le rho (level : Int) hρ
  have hsource := sourceFailure_diffusive_weight_le R level rho p hstart hρ
    hleft (by omega) hbottom htop
  have hp'y : p'.2.1 = p.2.1 := by
    have hy := congrArg Prod.snd hmirror
    dsimp [isingLeapfrogBoxInt, reflectedEndpoint] at hy
    exact_mod_cast hy
  have hbottom' : rho ≤ p'.2.1 := by omega
  have htop' : p'.2.1 + rho ≤ R := by omega
  have hmirrorFail := mirrorFailure_diffusive_weight_le R level rho p p'
    hstart hmirror hρ (lt_of_lt_of_le hρ hleft) hright hbottom' htop'
  have hden : 0 < (4 : Real) ^ (rho * rho) := by positivity
  calc
    _ ≤ (Nat.card (IsingLeapfrogChoiceNoHitAll (rho * rho)
          (isingLeapfrogBoxInt p).1 (level : Int)) +
        Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho) p
          (level : Int)) +
        Nat.card (IsingStoppedCouplingMirrorFailureFamily R (rho * rho) p p'
          (level : Int))) / (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcoverReal hden.le
    _ = Nat.card (IsingLeapfrogChoiceNoHitAll (rho * rho)
          (isingLeapfrogBoxInt p).1 (level : Int)) /
          (4 : Real) ^ (rho * rho) +
        Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho) p
          (level : Int)) / (4 : Real) ^ (rho * rho) +
        Nat.card (IsingStoppedCouplingMirrorFailureFamily R (rho * rho) p p'
          (level : Int)) / (4 : Real) ^ (rho * rho) := by ring
    _ ≤ 4 / (rho : Real) + 17 / (rho : Real) + 17 / (rho : Real) :=
      add_le_add (add_le_add hnohit hsource) hmirrorFail
    _ = 38 / (rho : Real) := by ring


theorem isingLeapfrogStoppedKernel_reflectionCoupling_l1_le
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int) :
    ∑ q : IsingLeapfrogBox R,
      |isingLeapfrogStoppedKernel R t p q -
        isingLeapfrogStoppedKernel R t p' q| ≤
      2 * (Nat.card
        (IsingLeapfrogStoppedCouplingBadFamily R t p p' level) : Real) /
          (4 : Real) ^ t := by
  classical
  letI := Fintype.ofFinite (IsingLeapfrogChoiceStringFamily t)
  let e := isingLeapfrogCouplingChoiceEquiv t
    (isingLeapfrogBoxInt p) level
  let f : IsingLeapfrogChoiceStringFamily t → IsingLeapfrogBox R :=
    fun w => isingLeapfrogChoiceRun R p w.1
  let g : IsingLeapfrogChoiceStringFamily t → IsingLeapfrogBox R :=
    fun w => isingLeapfrogChoiceRun R p' w.1
  have hcount := finiteUniformCoupling_fiber_l1_le e f g
  have hden : 0 < (4 : Real) ^ t := by positivity
  have hfiber (q : IsingLeapfrogBox R) :
      Nat.card (IsingLeapfrogStoppedChoicePathFamily R t p q) =
        Nat.card {w : IsingLeapfrogChoiceStringFamily t // f w = q} := by
    exact Nat.card_congr
      (isingLeapfrogStoppedChoicePathFiberEquiv R t p q)
  have hfiber' (q : IsingLeapfrogBox R) :
      Nat.card (IsingLeapfrogStoppedChoicePathFamily R t p' q) =
        Nat.card {w : IsingLeapfrogChoiceStringFamily t // g w = q} := by
    exact Nat.card_congr
      (isingLeapfrogStoppedChoicePathFiberEquiv R t p' q)
  rw [show Nat.card
      (IsingLeapfrogStoppedCouplingBadFamily R t p p' level) =
      Nat.card {w : IsingLeapfrogChoiceStringFamily t // f w ≠ g (e w)} by
        rfl]
  simp_rw [isingLeapfrogStoppedKernel_eq_natCard_choicePath_div]
  simp_rw [hfiber, hfiber']
  calc
    (∑ q : IsingLeapfrogBox R,
      |((Nat.card {w : IsingLeapfrogChoiceStringFamily t // f w = q} : Real) /
          (4 : Real) ^ t) -
        ((Nat.card {w : IsingLeapfrogChoiceStringFamily t // g w = q} : Real) /
          (4 : Real) ^ t)|) =
      (∑ q : IsingLeapfrogBox R,
        |((Nat.card {w : IsingLeapfrogChoiceStringFamily t // f w = q} : Real) -
          (Nat.card {w : IsingLeapfrogChoiceStringFamily t // g w = q} : Real))|) /
            (4 : Real) ^ t := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro q hq
      rw [div_sub_div_same, abs_div, abs_of_pos hden]
    _ ≤ (2 * (Nat.card
        {w : IsingLeapfrogChoiceStringFamily t // f w ≠ g (e w)} : Real)) /
          (4 : Real) ^ t := by
      exact div_le_div_of_nonneg_right hcount hden.le


theorem isingLeapfrogStoppedKernel_reflectedStart_diffusive_l1_le
    (R level rho : Nat) (p p' : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho ≤ level) (hright : level + rho ≤ R)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R) :
    (∑ q : IsingLeapfrogBox R,
      |isingLeapfrogStoppedKernel R (rho * rho) p q -
        isingLeapfrogStoppedKernel R (rho * rho) p' q|) ≤
      76 / (rho : Real) := by
  have hcouple := isingLeapfrogStoppedKernel_reflectionCoupling_l1_le R
    (rho * rho) p p' (level : Int)
  have hbad := stoppedCouplingBad_diffusive_weight_le R level rho p p'
    hstart hmirror hρ hleft hright hbottom htop
  calc
    _ ≤ 2 * (Nat.card (IsingLeapfrogStoppedCouplingBadFamily R
        (rho * rho) p p' (level : Int)) : Real) /
          (4 : Real) ^ (rho * rho) := hcouple
    _ = 2 * ((Nat.card (IsingLeapfrogStoppedCouplingBadFamily R
        (rho * rho) p p' (level : Int)) : Real) /
          (4 : Real) ^ (rho * rho)) := by ring
    _ ≤ 2 * (38 / (rho : Real)) := mul_le_mul_of_nonneg_left hbad
      (show (0 : Real) ≤ 2 by norm_num)
    _ = 76 / (rho : Real) := by ring

end
end StatMech.Universality
