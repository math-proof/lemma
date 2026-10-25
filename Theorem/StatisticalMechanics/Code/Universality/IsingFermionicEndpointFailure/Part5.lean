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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part5


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem sourceFailureOutputTransverseCover_value
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R)
    (w : IsingSourceFailureOutputAtFamily R t p q (level : Int)) :
    tailDependentEndpointRaceValue R t rho p q (level : Int)
      (sourceFailureOutputTransverseCover R level rho t p q hstart hρ
        hbottom htop hqVertical w) = w.1.1 := by
  exact Classical.choose_spec (exists_sourceFailureOutputTransverseCover
    R level rho t p q hstart hρ hbottom htop hqVertical w)

theorem sourceFailureOutputTransverseCover_injective
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R) :
    Function.Injective (sourceFailureOutputTransverseCover R level rho t
      p q hstart hρ hbottom htop hqVertical) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  rw [← sourceFailureOutputTransverseCover_value R level rho t p q hstart
      hρ hbottom htop hqVertical a,
    ← sourceFailureOutputTransverseCover_value R level rho t p q hstart
      hρ hbottom htop hqVertical b, hab]


theorem sourceFailureOutputAt_vertical_diffusive_weight_le
    (R level rho : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R) :
    Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
        (level : Int)) / (4 : Real) ^ (rho * rho) <=
      24 / (rho : Real) ^ 2 := by
  have hcard := Nat.card_le_card_of_injective
    (sourceFailureOutputTransverseCover R level rho (rho * rho) p q hstart
      hρ hbottom htop hqVertical)
    (sourceFailureOutputTransverseCover_injective R level rho (rho * rho)
      p q hstart hρ hbottom htop hqVertical)
  have hcardReal :
      (Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
        (level : Int)) : Real) <=
      Nat.card (IsingTailDependentEndpointRaceFamily rho (rho * rho)
        (level : Int) (sourceEndpointRaceTarget R (rho * rho) rho p q)) := by
    exact_mod_cast hcard
  exact (div_le_div_of_nonneg_right hcardReal (by positivity)).trans
    (tailDependentEndpointRace_diffusive_weight_le rho rho (level : Int)
      (sourceEndpointRaceTarget R (rho * rho) rho p q) hρ (le_refl _))

end
end StatMech.Universality
