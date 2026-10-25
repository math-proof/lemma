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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part28


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem mirrorNoHitOutputReflectX_injective
    (R t level : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level <= R) :
    Function.Injective
      (mirrorNoHitOutputReflectX R t level p p' q hstart hmirror hlevelR) := by
  intro a b hab
  apply Subtype.ext
  have hv := congrArg
    (fun z : IsingSourceChoiceNoHitOutputAtFamily R t
      (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
      ((R - level : Nat) : Int) => z.1) hab
  exact hv

theorem mirrorChoiceNoHitOutputAt_boundary_diffusive_weight_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hright : level + rho <= R)
    (hbottom : rho <= p'.2.1) (htop : p'.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingMirrorChoiceNoHitOutputAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  have hlevelR : level <= R := by omega
  have hcard := Nat.card_le_card_of_injective
    (mirrorNoHitOutputReflectX R (rho * rho) level p p' q hstart hmirror
      hlevelR)
    (mirrorNoHitOutputReflectX_injective R (rho * rho) level p p' q hstart
      hmirror hlevelR)
  have hcardReal :
      (Nat.card (IsingMirrorChoiceNoHitOutputAtFamily
        R (rho * rho) p p' q (level : Int)) : Real) <=
      Nat.card (IsingSourceChoiceNoHitOutputAtFamily R (rho * rho)
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        ((R - level : Nat) : Int)) := by
    exact_mod_cast hcard
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
  exact (div_le_div_of_nonneg_right hcardReal (by positivity)).trans
    (sourceChoiceNoHitOutputAt_boundary_diffusive_weight_le R (R - level) rho
      (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
      hrefStart hρ (by omega) (Nat.sub_le ..) hrefBottom hrefTop hrefBoundary)

end
end StatMech.Universality
