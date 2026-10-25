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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part7


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem sourceFailureOutputFarCover_value
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0)
    (w : IsingSourceFailureOutputAtFamily R t p q (level : Int)) :
    endpointFarEscapeWitnessValue level t
      (isingLeapfrogBoxInt p).2 (isingLeapfrogBoxInt q).2
      (sourceFailureOutputFarCover R level t p q hstart hqLeft w) = w.1.1 := by
  exact Classical.choose_spec
    (exists_sourceFailureOutputFarCover R level t p q hstart hqLeft w)

theorem sourceFailureOutputFarCover_injective
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0) :
    Function.Injective
      (sourceFailureOutputFarCover R level t p q hstart hqLeft) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  rw [← sourceFailureOutputFarCover_value R level t p q hstart hqLeft a,
    ← sourceFailureOutputFarCover_value R level t p q hstart hqLeft b, h]


theorem sourceFailureOutputAt_left_diffusive_weight_le
    (R level rho : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0) (hρ : 0 < rho) (hlevel : rho ≤ level) :
    Nat.card (IsingSourceFailureOutputAtFamily
          R (rho * rho) p q (level : Int)) /
        (4 : Real) ^ (rho * rho) ≤
      468 / (rho : Real) ^ 2 := by
  have hcard := Nat.card_le_card_of_injective
    (sourceFailureOutputFarCover R level (rho * rho) p q hstart hqLeft)
    (sourceFailureOutputFarCover_injective
      R level (rho * rho) p q hstart hqLeft)
  have hcardReal :
      (Nat.card (IsingSourceFailureOutputAtFamily
        R (rho * rho) p q (level : Int)) : Real) ≤
      Nat.card (IsingEndpointFarEscapeWitnessFamily level (rho * rho)
        (isingLeapfrogBoxInt p).2 (isingLeapfrogBoxInt q).2) := by
    exact_mod_cast hcard
  exact (div_le_div_of_nonneg_right hcardReal (by positivity)).trans
    (endpointFarEscapeWitness_diffusive_weight_le rho level
      (isingLeapfrogBoxInt p).2 (isingLeapfrogBoxInt q).2 hρ hlevel)

theorem sourceFailureOutputAt_right_card_eq_zero
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hlevelR : level < R) (hqRight : q.1.1 = R) :
    Nat.card (IsingSourceFailureOutputAtFamily R t p q (level : Int)) = 0 := by
  apply Nat.card_eq_zero.mpr
  left
  constructor
  intro w
  have hstartLt : (isingLeapfrogBoxInt p).1 < (level : Int) := by omega
  rcases sourceFailure_boundary_data R t p (level : Int) hstartLt w.1 with
    ⟨split, j, hsplit, hj, hb, hminimal, hxlt, hrun⟩
  have hjT : j <= t := by
    have hlen := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
      w.1.1.2] at hlen
    omega
  have hprefixQ : isingLeapfrogChoiceRun R p (w.1.1.1.take j) = q := by
    have hdecomp : w.1.1.1 = w.1.1.1.take j ++ w.1.1.1.drop j :=
      (List.take_append_drop j w.1.1.1).symm
    have hfull : isingLeapfrogChoiceRun R p w.1.1.1 =
        isingLeapfrogChoiceRun R p (w.1.1.1.take j) := by
      calc
        _ = isingLeapfrogChoiceRun R p
            (w.1.1.1.take j ++ w.1.1.1.drop j) := by rw [← hdecomp]
        _ = isingLeapfrogChoiceRun R
            (isingLeapfrogChoiceRun R p (w.1.1.1.take j))
              (w.1.1.1.drop j) := isingLeapfrogChoiceRun_append_full ..
        _ = _ :=
          isingLeapfrogChoiceRun_of_boundary_endpointFailure R _ hb _
    exact hfull.symm.trans w.2
  have hx := congrArg Prod.fst hrun
  rw [hprefixQ] at hx
  change ((q.1.1 : Nat) : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
      (isingLeapfrogChoiceSteps (w.1.1.1.take j))).1 at hx
  have hqInt : ((q.1.1 : Nat) : Int) = R := by exact_mod_cast hqRight
  rw [hqInt] at hx
  omega


theorem sourceFailureOutputAt_boundary_diffusive_weight_le
    (R level rho : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hleft : rho <= level) (hlevelR : level < R)
    (hbottom : rho <= p.2.1) (htop : p.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q
        (level : Int)) / (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  unfold isingLeapfrogBoxBoundary at hqBoundary
  rcases hqBoundary with hqLeft | hqRight | hqBottom | hqTop
  · exact sourceFailureOutputAt_left_diffusive_weight_le R level rho p q
      hstart hqLeft hρ hleft
  · rw [sourceFailureOutputAt_right_card_eq_zero R level (rho * rho) p q
      hstart hlevelR (by omega)]
    have hnonneg : 0 <= (468 : Real) / (rho : Real) ^ 2 := by positivity
    simpa using hnonneg
  · exact (sourceFailureOutputAt_vertical_diffusive_weight_le R level rho p q
      hstart hρ hbottom htop (Or.inl hqBottom)).trans (by
        apply div_le_div_of_nonneg_right (by norm_num)
        positivity)
  · exact (sourceFailureOutputAt_vertical_diffusive_weight_le R level rho p q
      hstart hρ hbottom htop (Or.inr (by omega))).trans (by
        apply div_le_div_of_nonneg_right (by norm_num)
        positivity)


end
end StatMech.Universality
