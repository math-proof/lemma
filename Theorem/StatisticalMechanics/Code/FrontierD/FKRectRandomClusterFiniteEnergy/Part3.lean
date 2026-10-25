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
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFiniteEnergy.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

theorem fkRectGraphCriticalClosedMass_reindex
    (R : FKRectTorus) (q : Real)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
    (he : e ∉ I) :
    fkRectGraphCriticalClosedMass R q I =
      ∑ eta ∈ fkRectGraphClosedFibre R e I,
        (fkRectGraphCriticalRandomClusterProb R q
          (setOpen e eta) +
          fkRectGraphCriticalRandomClusterProb R q
            (setClosed e eta)) := by
  classical
  unfold fkRectGraphCriticalClosedMass fkRectGraphClosedFibre
  rw [Finset.sum_add_distrib]
  have hclosed :
      (∑ eta ∈ Finset.univ.filter
          (fun eta : FKRectGraphConfiguration R =>
            eta e = false ∧ ∀ e' ∈ I, eta e' = false),
        fkRectGraphCriticalRandomClusterProb R q
          (setClosed e eta)) =
      ∑ omega ∈ Finset.univ.filter
          (fun omega : FKRectGraphConfiguration R =>
            (∀ e' ∈ I, omega e' = false) ∧ omega e = false),
        fkRectGraphCriticalRandomClusterProb R q omega := by
    apply Finset.sum_nbij' (fun eta => eta) (fun omega => omega)
    · intro eta heta
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta ⊢
      exact ⟨heta.2, heta.1⟩
    · intro omega homega
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega ⊢
      exact ⟨homega.2, homega.1⟩
    · intro eta _
      rfl
    · intro omega _
      rfl
    · intro eta heta
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
      congr 1
      funext x
      by_cases hx : x = e
      · subst x
        simp [heta.1]
      · rw [setClosed_of_ne hx]
  have hopen :
      (∑ eta ∈ Finset.univ.filter
          (fun eta : FKRectGraphConfiguration R =>
            eta e = false ∧ ∀ e' ∈ I, eta e' = false),
        fkRectGraphCriticalRandomClusterProb R q
          (setOpen e eta)) =
      ∑ omega ∈ Finset.univ.filter
          (fun omega : FKRectGraphConfiguration R =>
            (∀ e' ∈ I, omega e' = false) ∧ omega e = true),
        fkRectGraphCriticalRandomClusterProb R q omega := by
    apply Finset.sum_nbij'
      (fun eta => setOpen e eta)
      (fun omega => setClosed e omega)
    · intro eta heta
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta ⊢
      refine ⟨fun e' he' => ?_, by simp⟩
      have hne : e' ≠ e := fun h => he (h ▸ he')
      rw [setOpen_of_ne hne]
      exact heta.2 e' he'
    · intro omega homega
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega ⊢
      refine ⟨by simp, fun e' he' => ?_⟩
      have hne : e' ≠ e := fun h => he (h ▸ he')
      rw [setClosed_of_ne hne]
      exact homega.1 e' he'
    · intro eta heta
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
      funext x
      by_cases hx : x = e
      · subst x
        simp [heta.1]
      · rw [setClosed_of_ne hx, setOpen_of_ne hx]
    · intro omega homega
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega
      funext x
      by_cases hx : x = e
      · subst x
        simp [homega.2]
      · rw [setOpen_of_ne hx, setClosed_of_ne hx]
    · intro eta _
      rfl
  rw [hopen, hclosed]
  have htrue :
      Finset.univ.filter
          (fun omega : FKRectGraphConfiguration R =>
            (∀ e' ∈ I, omega e' = false) ∧ omega e = true) =
        (Finset.univ.filter fun omega : FKRectGraphConfiguration R =>
          ∀ e' ∈ I, omega e' = false).filter
            (fun omega => ¬ omega e = false) := by
    ext omega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.not_eq_false]
  have hfalse :
      Finset.univ.filter
          (fun omega : FKRectGraphConfiguration R =>
            (∀ e' ∈ I, omega e' = false) ∧ omega e = false) =
        (Finset.univ.filter fun omega : FKRectGraphConfiguration R =>
          ∀ e' ∈ I, omega e' = false).filter
            (fun omega => omega e = false) := by
    ext omega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [htrue, hfalse, add_comm]
  exact (Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter fun omega : FKRectGraphConfiguration R =>
      ∀ e' ∈ I, omega e' = false)
    (fun omega => omega e = false)
    (fkRectGraphCriticalRandomClusterProb R q)).symm

theorem fkRectGraphCriticalClosedMass_insert_reindex
    (R : FKRectTorus) (q : Real)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    fkRectGraphCriticalClosedMass R q (insert e I) =
      ∑ eta ∈ fkRectGraphClosedFibre R e I,
        fkRectGraphCriticalRandomClusterProb R q
          (setClosed e eta) := by
  classical
  unfold fkRectGraphCriticalClosedMass fkRectGraphClosedFibre
  apply Finset.sum_nbij' (fun omega => omega) (fun eta => eta)
  · intro omega homega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.forall_mem_insert] at homega ⊢
    exact ⟨homega.1, homega.2⟩
  · intro eta heta
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.forall_mem_insert] at heta ⊢
    exact ⟨heta.1, heta.2⟩
  · intro omega _
    rfl
  · intro eta _
    rfl
  · intro omega homega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.forall_mem_insert] at homega
    congr 1
    funext x
    by_cases hx : x = e
    · subst x
      simp [homega.1]
    · rw [setClosed_of_ne hx]

theorem fkRectGraphCritical_cFE_mul_closedMass_le_insert
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
    (he : e ∉ I) :
    FK.cFE (fkRectCriticalP q) q *
        fkRectGraphCriticalClosedMass R q I ≤
      fkRectGraphCriticalClosedMass R q (insert e I) := by
  rw [fkRectGraphCriticalClosedMass_reindex R q e he,
    fkRectGraphCriticalClosedMass_insert_reindex R q e I,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro eta heta
  exact fkRectGraphCriticalProb_setClosed_ge R hq e eta


theorem fkRectGraphCritical_cFE_pow_le_closedMass
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    FK.cFE (fkRectCriticalP q) q ^ I.card ≤
      fkRectGraphCriticalClosedMass R q I := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  classical
  induction I using Finset.induction with
  | empty =>
      rw [Finset.card_empty, pow_zero,
        fkRectGraphCriticalClosedMass_empty R hq0]
  | @insert e I he ih =>
      rw [Finset.card_insert_of_notMem he, pow_succ]
      calc
        FK.cFE (fkRectCriticalP q) q ^ I.card *
              FK.cFE (fkRectCriticalP q) q =
            FK.cFE (fkRectCriticalP q) q *
              FK.cFE (fkRectCriticalP q) q ^ I.card := by ring
        _ ≤ FK.cFE (fkRectCriticalP q) q *
              fkRectGraphCriticalClosedMass R q I :=
          mul_le_mul_of_nonneg_left ih
            (FK.cFE_pos (fkRectCriticalP_pos hq0)
              (fkRectCriticalP_lt_one hq0) hq).le
        _ ≤ fkRectGraphCriticalClosedMass R q (insert e I) :=
          fkRectGraphCritical_cFE_mul_closedMass_le_insert R hq e he


end
end StatMech.FrontierD
