/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part21


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem sourceFailureCoverValue_apply
    (R level rho t : Nat) (p : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hlevel : 0 < level) (hlevelR : level < R) (hρ : 0 < rho)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R)
    (w : IsingStoppedCouplingSourceFailureFamily R t p (level : Int)) :
    sourceFailureCoverValue level rho t
      (sourceFailureCover R level rho t p hstart hlevel hlevelR hρ
        hbottom htop w) = w.1 := by
  classical
  unfold sourceFailureCover
  by_cases hh : ∃ z : IsingLeapfrogHorizontalEscapeFamily level t, z.1 = w.1
  · rw [dif_pos hh]
    exact (Classical.choose_spec hh)
  · rw [dif_neg hh]
    exact Classical.choose_spec
      ((sourceFailure_horizontal_or_transverse R level rho t p hstart hlevel
        hlevelR hρ hbottom htop w).resolve_left hh)

theorem sourceFailureCover_injective
    (R level rho t : Nat) (p : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hlevel : 0 < level) (hlevelR : level < R) (hρ : 0 < rho)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R) :
    Function.Injective
      (sourceFailureCover R level rho t p hstart hlevel hlevelR hρ
        hbottom htop) := by
  intro a b hab
  apply Subtype.ext
  rw [← sourceFailureCoverValue_apply R level rho t p hstart hlevel hlevelR
      hρ hbottom htop a,
    ← sourceFailureCoverValue_apply R level rho t p hstart hlevel hlevelR
      hρ hbottom htop b,
    hab]

theorem natCard_sourceFailure_le_horizontal_add_transverse
    (R level rho t : Nat) (p : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hlevel : 0 < level) (hlevelR : level < R) (hρ : 0 < rho)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R) :
    Nat.card (IsingStoppedCouplingSourceFailureFamily R t p (level : Int)) ≤
      Nat.card (IsingLeapfrogHorizontalEscapeFamily level t) +
        Nat.card (IsingTransverseRaceWitnessFamily rho t (level : Int)) := by
  calc
    _ ≤ Nat.card (IsingLeapfrogHorizontalEscapeFamily level t ⊕
        IsingTransverseRaceWitnessFamily rho t (level : Int)) :=
      Nat.card_le_card_of_injective
        (sourceFailureCover R level rho t p hstart hlevel hlevelR hρ
          hbottom htop)
        (sourceFailureCover_injective R level rho t p hstart hlevel hlevelR hρ
          hbottom htop)
    _ = _ := by rw [Nat.card_sum]

theorem sourceFailure_diffusive_weight_le
    (R level rho : Nat) (p : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hleft : rho ≤ level) (hright : level < R)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R) :
    Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho) p
        (level : Int)) / (4 : Real) ^ (rho * rho) ≤ 17 / (rho : Real) := by
  have hlevel : 0 < level := lt_of_lt_of_le hρ hleft
  have hcard := natCard_sourceFailure_le_horizontal_add_transverse
    R level rho (rho * rho) p hstart hlevel hright hρ hbottom htop
  have hcardReal :
      (Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho) p
        (level : Int)) : Real) ≤
      Nat.card (IsingLeapfrogHorizontalEscapeFamily level (rho * rho)) +
        Nat.card (IsingTransverseRaceWitnessFamily rho (rho * rho)
          (level : Int)) := by exact_mod_cast hcard
  have hden : 0 < (4 : Real) ^ (rho * rho) := by positivity
  have hhor := horizontalEscape_weight_le_inv level (rho * rho) hlevel
  have htrans := transverseRaceWitness_diffusive_weight_le rho rho
    (level : Int) hρ (le_refl _)
  have hρReal : 0 < (rho : Real) := by positivity
  have hlevelReal : (rho : Real) ≤ level := by exact_mod_cast hleft
  have hinv : 1 / (level : Real) ≤ 1 / (rho : Real) :=
    one_div_le_one_div_of_le hρReal hlevelReal
  calc
    _ ≤ (Nat.card (IsingLeapfrogHorizontalEscapeFamily level (rho * rho)) +
        Nat.card (IsingTransverseRaceWitnessFamily rho (rho * rho)
          (level : Int))) / (4 : Real) ^ (rho * rho) :=
      div_le_div_of_nonneg_right hcardReal hden.le
    _ = Nat.card (IsingLeapfrogHorizontalEscapeFamily level (rho * rho)) /
          (4 : Real) ^ (rho * rho) +
        Nat.card (IsingTransverseRaceWitnessFamily rho (rho * rho)
          (level : Int)) / (4 : Real) ^ (rho * rho) := by rw [add_div]
    _ ≤ 1 / (level : Real) + 16 / (rho : Real) := add_le_add hhor htrans
    _ ≤ 1 / (rho : Real) + 16 / (rho : Real) := add_le_add hinv (le_refl _)
    _ = 17 / (rho : Real) := by ring


end
end StatMech.Universality
