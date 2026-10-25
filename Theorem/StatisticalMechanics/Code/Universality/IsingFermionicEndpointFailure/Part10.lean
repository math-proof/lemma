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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part11


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem sourceFailureAtAlignedCover_of_rightHalf_value
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level < R) (hhalf : R <= 2 * level)
    (w : IsingStoppedCouplingSourceFailureAtFamily R t p p' q
      (level : Int)) :
    alignedFailureOutputValue R t p p' q (level : Int)
      (sourceFailureAtAlignedCover_of_rightHalf R level t p p' q hstart
        hmirror hlevelR hhalf w) = w.1 := by
  exact Classical.choose_spec
    (exists_sourceFailureAtAlignedCover_of_rightHalf R level t p p' q
      hstart hmirror hlevelR hhalf w)

theorem sourceFailureAtAlignedCover_of_rightHalf_injective
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level < R) (hhalf : R <= 2 * level) :
    Function.Injective (sourceFailureAtAlignedCover_of_rightHalf R level t
      p p' q hstart hmirror hlevelR hhalf) := by
  intro a b hab
  apply Subtype.ext
  rw [← sourceFailureAtAlignedCover_of_rightHalf_value R level t p p' q
      hstart hmirror hlevelR hhalf a,
    ← sourceFailureAtAlignedCover_of_rightHalf_value R level t p p' q
      hstart hmirror hlevelR hhalf b, hab]

theorem sourceFailureAt_boundary_diffusive_weight_le_of_rightHalf
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level) (hlevelR : level < R)
    (hright : level + rho <= R) (hhalf : R <= 2 * level)
    (hbottom : rho <= p.2.1) (htop : p.2.1 + rho <= R)
    (hbottom' : rho <= p'.2.1) (htop' : p'.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
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
    _ <= 468 / (rho : Real) ^ 2 + 468 / (rho : Real) ^ 2 :=
      add_le_add
        (sourceFailureOutputAt_boundary_diffusive_weight_le R level rho p q
          hstart hρ hleft hlevelR hbottom htop hqBoundary)
        (mirrorFailureOutputAt_boundary_diffusive_weight_le R level rho
          p p' q hstart hmirror hρ (lt_of_lt_of_le hρ hleft) hright
          hbottom' htop' hqBoundary)
    _ = 936 / (rho : Real) ^ 2 := by ring


end
end StatMech.Universality
