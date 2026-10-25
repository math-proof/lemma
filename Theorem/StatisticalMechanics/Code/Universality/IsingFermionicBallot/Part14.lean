/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part17


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem survivalExceptionalMirrorBoxSigmaToAll_injective
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    Function.Injective
      (survivalExceptionalMirrorBoxSigmaToAll R t p level) := by
  intro a b h
  rcases Sigma.ext_iff.mp h with ⟨htarget, hw⟩
  exact Sigma.ext (isingLeapfrogBoxInt_injective htarget) hw


theorem isingLeapfrogKilledKernel_reflectedStart_l1_le
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    (∑ q, |isingLeapfrogKilledKernel R t p q -
        isingLeapfrogKilledKernel R t p' q|) ≤
      Nat.card (SurvivalExceptionalFirstHitFamilyAll R
          (isingLeapfrogBoxInt p) level t) / (4 : Real) ^ t +
        Nat.card (SurvivalExceptionalMirrorFamilyAll R
          (isingLeapfrogBoxInt p) level t) / (4 : Real) ^ t +
        Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p level) /
          (4 : Real) ^ t +
        Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p' level) /
          (4 : Real) ^ t := by
  let D := (4 : Real) ^ t
  have hD : 0 < D := by positivity
  have hpoint (q : IsingLeapfrogBox R) :
      |isingLeapfrogKilledKernel R t p q -
          isingLeapfrogKilledKernel R t p' q| ≤
        Nat.card (SurvivalExceptionalFirstHitFamily R
            (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) / D +
          Nat.card (SurvivalExceptionalMirrorFamily R
            (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) / D +
          Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) / D +
          Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p' q level) / D := by
    have hbase := isingLeapfrogKilledKernel_reflectedStart_abs_le
      R t p p' q level hmirror
    have hdist := natDist_survivingFirstHitFamily_le_exceptions R
      (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)
    have hdistReal :
        (Nat.dist
          (Nat.card (SurvivingFirstHitFamily R (isingLeapfrogBoxInt p)
            level t (isingLeapfrogBoxInt q)))
          (Nat.card (SurvivingFirstHitFamily R
            (reflectedEndpoint level (isingLeapfrogBoxInt p)) level t
            (isingLeapfrogBoxInt q))) : Real) ≤
          Nat.card (SurvivalExceptionalFirstHitFamily R
            (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) +
          Nat.card (SurvivalExceptionalMirrorFamily R
            (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) := by
      exact_mod_cast hdist
    have hdiv := div_le_div_of_nonneg_right hdistReal hD.le
    dsimp [D] at hbase ⊢
    calc
      _ ≤ _ := hbase
      _ ≤ (Nat.card (SurvivalExceptionalFirstHitFamily R
              (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) +
            Nat.card (SurvivalExceptionalMirrorFamily R
              (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q))) /
            (4 : Real) ^ t +
          Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) /
            (4 : Real) ^ t +
          Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p' q level) /
            (4 : Real) ^ t := by
        dsimp [D] at hdiv
        exact add_le_add_left (add_le_add_left hdiv _) _
      _ = _ := by ring
  have hsum :
      (∑ q, |isingLeapfrogKilledKernel R t p q -
        isingLeapfrogKilledKernel R t p' q|) ≤
      ∑ q, (Nat.card (SurvivalExceptionalFirstHitFamily R
            (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) / D +
          Nat.card (SurvivalExceptionalMirrorFamily R
            (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) / D +
          Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) / D +
          Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p' q level) / D) :=
    Finset.sum_le_sum (fun q _ => hpoint q)
  simp only [Finset.sum_add_distrib] at hsum
  have hsourceNat :
      ∑ q : IsingLeapfrogBox R, Nat.card (SurvivalExceptionalFirstHitFamily R
          (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) ≤
        Nat.card (SurvivalExceptionalFirstHitFamilyAll R
          (isingLeapfrogBoxInt p) level t) := by
    rw [← Nat.card_sigma]
    exact Nat.card_le_card_of_injective
      (survivalExceptionalFirstHitBoxSigmaToAll R t p level)
      (survivalExceptionalFirstHitBoxSigmaToAll_injective R t p level)
  have hmirrorNat :
      ∑ q : IsingLeapfrogBox R, Nat.card (SurvivalExceptionalMirrorFamily R
          (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) ≤
        Nat.card (SurvivalExceptionalMirrorFamilyAll R
          (isingLeapfrogBoxInt p) level t) := by
    rw [← Nat.card_sigma]
    exact Nat.card_le_card_of_injective
      (survivalExceptionalMirrorBoxSigmaToAll R t p level)
      (survivalExceptionalMirrorBoxSigmaToAll_injective R t p level)
  have hsourceReal :
      (∑ q : IsingLeapfrogBox R, (Nat.card (SurvivalExceptionalFirstHitFamily R
          (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) : Real)) / D ≤
        Nat.card (SurvivalExceptionalFirstHitFamilyAll R
          (isingLeapfrogBoxInt p) level t) / D := by
    apply div_le_div_of_nonneg_right _ hD.le
    exact_mod_cast hsourceNat
  have hmirrorReal :
      (∑ q : IsingLeapfrogBox R, (Nat.card (SurvivalExceptionalMirrorFamily R
          (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) : Real)) / D ≤
        Nat.card (SurvivalExceptionalMirrorFamilyAll R
          (isingLeapfrogBoxInt p) level t) / D := by
    apply div_le_div_of_nonneg_right _ hD.le
    exact_mod_cast hmirrorNat
  have hnohit := natCard_killedChoiceNoHitAll_eq_sum R t p level
  have hnohit' := natCard_killedChoiceNoHitAll_eq_sum R t p' level
  have hnohitReal :
      ∑ q, (Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) :
        Real) = Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p level) := by
    exact_mod_cast hnohit.symm
  have hnohitReal' :
      ∑ q, (Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p' q level) :
        Real) = Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p' level) := by
    exact_mod_cast hnohit'.symm
  dsimp [D] at hsum hsourceReal hmirrorReal ⊢
  simp_rw [← Finset.sum_div] at hsum
  rw [hnohitReal, hnohitReal'] at hsum
  exact le_trans hsum (by linarith)


theorem isingLeapfrogKilledKernel_reflectedStart_diffusive_l1_le
    (R level ρ : Nat) (p p' : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < ρ) (hleft : ρ + 1 ≤ level)
    (hright : level + 1 + ρ ≤ R) :
    (∑ q, |isingLeapfrogKilledKernel R (ρ * ρ) p q -
        isingLeapfrogKilledKernel R (ρ * ρ) p' q|) ≤
      10 / (ρ : Real) := by
  have hbase := isingLeapfrogKilledKernel_reflectedStart_l1_le R
    (ρ * ρ) p p' (level : Int) hmirror
  have hlevel : 0 < level := by omega
  have hgap : level + 1 < R := by omega
  have hsource :=
    survivalExceptionalFirstHitFamilyAll_weight_le_inv_rightGap R level
      (ρ * ρ) (isingLeapfrogBoxInt p) hstart hlevel hgap
  have hmirrorExc :=
    survivalExceptionalMirrorFamilyAll_weight_le_inv_leftGap R level
      (ρ * ρ) (isingLeapfrogBoxInt p) hstart hlevel
  have hnohit := killedChoiceNoHitAll_diffusive_weight_le R ρ p
    (level : Int) hstart hρ
  have hp' : (isingLeapfrogBoxInt p').1 = (level : Int) + 1 := by
    rw [hmirror]
    unfold reflectedEndpoint
    dsimp
    omega
  have hnohit' := killedChoiceNoHitAll_diffusive_weight_le_upper R ρ p'
    (level : Int) hp' hρ
  have hρReal : 0 < (ρ : Real) := by positivity
  have hrightGap : (ρ : Real) ≤ (R - level : Nat) := by
    exact_mod_cast (show ρ ≤ R - level by omega)
  have hleftGap : (ρ : Real) ≤ level := by
    exact_mod_cast (show ρ ≤ level by omega)
  have hinvRight : 1 / ((R - level : Nat) : Real) ≤
      1 / (ρ : Real) := one_div_le_one_div_of_le hρReal hrightGap
  have hinvLeft : 1 / (level : Real) ≤
      1 / (ρ : Real) := one_div_le_one_div_of_le hρReal hleftGap
  calc
    _ ≤ _ := hbase
    _ ≤ 1 / ((R - level : Nat) : Real) + 1 / (level : Real) +
        4 / (ρ : Real) + 4 / (ρ : Real) := by
      exact add_le_add (add_le_add (add_le_add hsource hmirrorExc) hnohit) hnohit'
    _ ≤ 1 / (ρ : Real) + 1 / (ρ : Real) +
        4 / (ρ : Real) + 4 / (ρ : Real) := by
      exact add_le_add (add_le_add (add_le_add hinvRight hinvLeft) (le_refl _))
        (le_refl _)
    _ = 10 / (ρ : Real) := by ring

end
end StatMech.Universality
