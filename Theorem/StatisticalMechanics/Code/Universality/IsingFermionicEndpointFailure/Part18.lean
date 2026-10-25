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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part21


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem mirrorOnlyOrderedCover_value
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q)
    (w : IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int)) :
    orderedFarEndpointValue (R - level) R t p.2 q.2
        (2 * (level : Int) - R) (q.1 : Int)
        (mirrorOnlyOrderedCover R level t p p' q hlevelR hstart hmirror hq w) =
      w.1 := by
  exact (Classical.choose_spec
    (exists_mirrorOnlyOrderedCover R level t p p' q hlevelR hstart hmirror hq w)).1

theorem mirrorOnlyOrderedCover_injective
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q) :
    Function.Injective
      (mirrorOnlyOrderedCover R level t p p' q hlevelR hstart hmirror hq) := by
  intro a b hab
  apply Subtype.ext
  rw [← mirrorOnlyOrderedCover_value R level t p p' q hlevelR hstart hmirror hq a,
    ← mirrorOnlyOrderedCover_value R level t p p' q hlevelR hstart hmirror hq b,
    hab]

theorem natCard_mirrorOnlySourceOutputAt_le_orderedFarEndpoint
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R t p p' q (level : Int)) <=
      Nat.card (IsingOrderedFarEndpointFamily (R - level) R t p.2 q.2
        (2 * (level : Int) - R) (q.1 : Int)) :=
  Nat.card_le_card_of_injective
    (mirrorOnlyOrderedCover R level t p p' q hlevelR hstart hmirror hq)
    (mirrorOnlyOrderedCover_injective R level t p p' q
      hlevelR hstart hmirror hq)

theorem mirrorOnlySourceOutputAt_vertical_diffusive_weight_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hright : level + rho <= R)
    (hqVertical : q.2.1 = 0 ∨ q.2.1 = R) :
    Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      7488 / (rho : Real) ^ 2 := by
  have hlevelR : level <= R := by omega
  have hq : isingLeapfrogBoxBoundary R q := by
    unfold isingLeapfrogBoxBoundary
    rcases hqVertical with hq | hq
    · right; right; left; exact hq
    · right; right; right; omega
  have hcard := natCard_mirrorOnlySourceOutputAt_le_orderedFarEndpoint
    R level (rho * rho) p p' q hlevelR hstart hmirror hq
  have hden : 0 <= (4 : Real) ^ (rho * rho) := by positivity
  calc
    Nat.card (IsingMirrorOnlySourceOutputAtFamily
        R (rho * rho) p p' q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      Nat.card (IsingOrderedFarEndpointFamily (R - level) R (rho * rho)
        p.2 q.2 (2 * (level : Int) - R) (q.1 : Int)) /
        (4 : Real) ^ (rho * rho) := by
      apply div_le_div_of_nonneg_right _ hden
      exact_mod_cast hcard
    _ <= 7488 / (rho : Real) ^ 2 := by
      apply orderedFarEndpoint_diffusive_weight_le rho (R - level) R p.2 q.2
        (2 * (level : Int) - R) (q.1 : Int) hρ (by omega)
      unfold isingLineBoxBoundary
      exact hqVertical

end
end StatMech.Universality
