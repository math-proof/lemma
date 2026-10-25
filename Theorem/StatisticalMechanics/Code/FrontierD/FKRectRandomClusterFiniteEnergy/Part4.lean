/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFKG.Part2
import Theorem.StatisticalMechanics.Code.FK.CircuitLowerBound.Part6
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFiniteEnergy.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

theorem fkRectGraphCriticalOpenMass_eq_expectation
    (R : FKRectTorus) (q : Real)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    fkRectGraphCriticalOpenMass R q I =
      ∑ eta, fkRectGraphCriticalRandomClusterProb R q eta *
        fkRectGraphOpenIndicator R I eta := by
  classical
  unfold fkRectGraphCriticalOpenMass fkRectGraphOpenIndicator
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro eta heta
  by_cases h : ∀ e ∈ I, eta e = true
  · simp [h]
  · simp [h]

theorem monotone_fkRectGraphOpenIndicator
    (R : FKRectTorus)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    Monotone (fkRectGraphOpenIndicator R I) := by
  intro eta zeta hetaZeta
  unfold fkRectGraphOpenIndicator
  by_cases heta : ∀ e ∈ I, eta e = true
  · have hzeta : ∀ e ∈ I, zeta e = true := by
      intro e he
      have hcoord := hetaZeta e
      rw [heta e he] at hcoord
      exact Bool.eq_true_of_true_le hcoord
    rw [if_pos heta, if_pos hzeta]
  · rw [if_neg heta]
    positivity

theorem fkRectGraphOpenIndicator_insert
    (R : FKRectTorus)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) :
    fkRectGraphOpenIndicator R (insert e I) eta =
      fkRectGraphOpenIndicator R {e} eta *
        fkRectGraphOpenIndicator R I eta := by
  classical
  unfold fkRectGraphOpenIndicator
  by_cases he : eta e = true <;>
    by_cases hI : ∀ a ∈ I, eta a = true <;>
    simp [he, hI]

theorem fkRectGraphCriticalOpenMass_singleton_reindex
    (R : FKRectTorus) (q : Real)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    fkRectGraphCriticalOpenMass R q {e} =
      ∑ eta ∈ fkRectGraphClosedFibre R e ∅,
        fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) := by
  classical
  unfold fkRectGraphCriticalOpenMass fkRectGraphClosedFibre
  apply Finset.sum_nbij'
    (fun omega => setClosed e omega) (fun eta => setOpen e eta)
  · intro omega homega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega ⊢
    simp
  · intro eta heta
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta ⊢
    simp
  · intro omega homega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega
    funext x
    by_cases hx : x = e
    · subst x
      rw [setOpen_self]
      exact (homega e (Finset.mem_singleton_self e)).symm
    · rw [setOpen_of_ne hx, setClosed_of_ne hx]
  · intro eta heta
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
    funext x
    by_cases hx : x = e
    · subst x
      simp [heta.1]
    · rw [setClosed_of_ne hx, setOpen_of_ne hx]
  · intro omega homega
    congr 1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega
    funext x
    by_cases hx : x = e
    · subst x
      rw [setOpen_self]
      exact homega e (Finset.mem_singleton_self e)
    · rw [setOpen_of_ne hx, setClosed_of_ne hx]

theorem fkRectGraphCritical_cFE_le_openMass_singleton
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    FK.cFE (fkRectCriticalP q) q ≤
      fkRectGraphCriticalOpenMass R q {e} := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have htotal := fkRectGraphCriticalClosedMass_reindex
    R q e (I := ∅) (by simp)
  rw [fkRectGraphCriticalClosedMass_empty R hq0] at htotal
  rw [fkRectGraphCriticalOpenMass_singleton_reindex R q e]
  calc
    FK.cFE (fkRectCriticalP q) q =
        FK.cFE (fkRectCriticalP q) q * 1 := by ring
    _ = FK.cFE (fkRectCriticalP q) q *
        ∑ eta ∈ fkRectGraphClosedFibre R e ∅,
          (fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) +
            fkRectGraphCriticalRandomClusterProb R q (setClosed e eta)) := by
      rw [htotal]
    _ = ∑ eta ∈ fkRectGraphClosedFibre R e ∅,
        FK.cFE (fkRectCriticalP q) q *
          (fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) +
            fkRectGraphCriticalRandomClusterProb R q (setClosed e eta)) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ eta ∈ fkRectGraphClosedFibre R e ∅,
        fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) := by
      apply Finset.sum_le_sum
      intro eta heta
      exact fkRectGraphCriticalProb_setOpen_ge R hq e eta

theorem fkRectGraphCriticalOpenMass_nonneg
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    0 ≤ fkRectGraphCriticalOpenMass R q I := by
  unfold fkRectGraphCriticalOpenMass
  exact Finset.sum_nonneg fun eta heta =>
    fkRectGraphCriticalRandomClusterProb_nonneg R hq eta

theorem fkRectGraphCritical_cFE_mul_openMass_le_insert
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    FK.cFE (fkRectCriticalP q) q *
        fkRectGraphCriticalOpenMass R q I ≤
      fkRectGraphCriticalOpenMass R q (insert e I) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hPA := fkRectGraphCritical_positivelyAssociated R hq
    (monotone_fkRectGraphOpenIndicator R {e})
    (monotone_fkRectGraphOpenIndicator R I)
  rw [← fkRectGraphCriticalOpenMass_eq_expectation R q {e},
    ← fkRectGraphCriticalOpenMass_eq_expectation R q I] at hPA
  rw [fkRectGraphCriticalOpenMass_eq_expectation R q (insert e I)]
  simp_rw [fkRectGraphOpenIndicator_insert R e I]
  exact (mul_le_mul_of_nonneg_right
      (fkRectGraphCritical_cFE_le_openMass_singleton R hq e)
      (fkRectGraphCriticalOpenMass_nonneg R hq0 I)).trans hPA


theorem fkRectGraphCritical_cFE_pow_le_openMass
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    FK.cFE (fkRectCriticalP q) q ^ I.card ≤
      fkRectGraphCriticalOpenMass R q I := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  classical
  induction I using Finset.induction with
  | empty =>
      rw [Finset.card_empty, pow_zero]
      unfold fkRectGraphCriticalOpenMass
      rw [show Finset.univ.filter
          (fun eta : FKRectGraphConfiguration R =>
            ∀ e ∈ (∅ : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}),
              eta e = true) = Finset.univ by ext eta; simp]
      exact (sum_fkRectGraphCriticalRandomClusterProb R hq0).ge
  | @insert e I he ih =>
      rw [Finset.card_insert_of_notMem he, pow_succ]
      calc
        FK.cFE (fkRectCriticalP q) q ^ I.card *
              FK.cFE (fkRectCriticalP q) q =
            FK.cFE (fkRectCriticalP q) q *
              FK.cFE (fkRectCriticalP q) q ^ I.card := by ring
        _ ≤ FK.cFE (fkRectCriticalP q) q *
              fkRectGraphCriticalOpenMass R q I :=
          mul_le_mul_of_nonneg_left ih
            (FK.cFE_pos (fkRectCriticalP_pos hq0)
              (fkRectCriticalP_lt_one hq0) hq).le
        _ ≤ fkRectGraphCriticalOpenMass R q (insert e I) :=
          fkRectGraphCritical_cFE_mul_openMass_le_insert R hq e I


end
end StatMech.FrontierD
