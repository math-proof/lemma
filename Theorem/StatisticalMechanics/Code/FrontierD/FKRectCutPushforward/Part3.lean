/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part3
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

section FiniteBoolPushforward

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] in
theorem finiteBoolForceClosed_empty (omega : ConfigSpace E) :
    finiteBoolForceClosed ∅ omega = omega := by
  funext e
  simp [finiteBoolForceClosed]

omit [Fintype E] in
theorem finiteBoolForceClosed_insert
    (I : Finset E) (e : E) (omega : ConfigSpace E) :
    finiteBoolForceClosed (insert e I) omega =
      finiteBoolForceClosed I (setClosed e omega) := by
  funext x
  by_cases hx : x = e <;> by_cases hxI : x ∈ I <;>
    simp [finiteBoolForceClosed, hx, hxI, setClosed_of_ne]

omit [Fintype E] in
theorem finiteBoolForceOpen_empty (omega : ConfigSpace E) :
    finiteBoolForceOpen ∅ omega = omega := by
  funext e
  simp [finiteBoolForceOpen]

omit [Fintype E] in
theorem finiteBoolForceOpen_insert
    (I : Finset E) (e : E) (omega : ConfigSpace E) :
    finiteBoolForceOpen (insert e I) omega =
      finiteBoolForceOpen I (setOpen e omega) := by
  funext x
  by_cases hx : x = e <;> by_cases hxI : x ∈ I <;>
    simp [finiteBoolForceOpen, hx, hxI, setOpen_of_ne]

theorem finiteBoolEventMass_preimage_setClosed
    (mu : ConfigSpace E → Real) (e : E) (A : Set (ConfigSpace E)) :
    finiteBoolEventMass mu (setClosed e ⁻¹' A) =
      ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E => eta e = false),
        A.indicator (fun _ => mu (setOpen e eta) + mu (setClosed e eta))
          (setClosed e eta) := by
  classical
  unfold finiteBoolEventMass
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (ConfigSpace E)) (fun eta => eta e = false)]
  calc
    _ = (∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E =>
            eta e = false),
          A.indicator (fun _ => mu (setClosed e eta)) (setClosed e eta)) +
        ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E =>
            eta e = false),
          A.indicator (fun _ => mu (setOpen e eta)) (setClosed e eta) := by
      congr 1
      · apply Finset.sum_bij (fun eta _ => eta)
        · intro eta heta
          simpa using heta
        · intro a ha b hb hab
          exact hab
        · intro eta heta
          exact ⟨eta, heta, rfl⟩
        · intro eta heta
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
          have hclose : setClosed e eta = eta := by
            funext x
            by_cases hx : x = e
            · subst x
              simp [heta]
            · rw [setClosed_of_ne hx]
          rw [hclose]
          by_cases hA : eta ∈ A <;>
            simp [Set.indicator, hA, hclose]
      · apply Finset.sum_bij (fun omega _ => setClosed e omega)
        · intro omega homega
          simp
        · intro omega homega rho hrho heq
          funext x
          by_cases hx : x = e
          · subst x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Bool.not_eq_false] at homega hrho
            rw [homega, hrho]
          · have hxval := congrFun heq x
            simpa [setClosed_of_ne hx] using hxval
        · intro eta heta
          refine ⟨setOpen e eta, by simp, ?_⟩
          funext x
          by_cases hx : x = e
          · subst x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
            simp [heta]
          · rw [setClosed_of_ne hx, setOpen_of_ne hx]
        · intro omega homega
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Bool.not_eq_false] at homega
          have hopenClosed : setOpen e (setClosed e omega) = omega := by
            funext x
            by_cases hx : x = e
            · subst x
              simp [homega]
            · rw [setOpen_of_ne hx, setClosed_of_ne hx]
          have hclosed : setClosed e (setClosed e omega) = setClosed e omega := by
            funext x
            by_cases hx : x = e
            · subst x
              simp
            · rw [setClosed_of_ne hx, setClosed_of_ne hx]
          rw [hopenClosed, hclosed]
          by_cases hA : setClosed e omega ∈ A <;>
            simp [Set.indicator, hA]
    _ = ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E =>
          eta e = false),
        A.indicator (fun _ => mu (setOpen e eta) + mu (setClosed e eta))
          (setClosed e eta) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro eta heta
      by_cases hA : setClosed e eta ∈ A <;> simp [hA, add_comm]

theorem finiteBoolEventMass_preimage_setOpen
    (mu : ConfigSpace E → Real) (e : E) (A : Set (ConfigSpace E)) :
    finiteBoolEventMass mu (setOpen e ⁻¹' A) =
      ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E => eta e = false),
        A.indicator (fun _ => mu (setOpen e eta) + mu (setClosed e eta))
          (setOpen e eta) := by
  classical
  unfold finiteBoolEventMass
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (ConfigSpace E)) (fun eta => eta e = false)]
  calc
    _ = (∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E =>
            eta e = false),
          A.indicator (fun _ => mu (setClosed e eta)) (setOpen e eta)) +
        ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E =>
            eta e = false),
          A.indicator (fun _ => mu (setOpen e eta)) (setOpen e eta) := by
      congr 1
      · apply Finset.sum_bij (fun eta _ => eta)
        · intro eta heta
          simpa using heta
        · intro a ha b hb hab
          exact hab
        · intro eta heta
          exact ⟨eta, heta, rfl⟩
        · intro eta heta
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
          have hclose : setClosed e eta = eta := by
            funext x
            by_cases hx : x = e
            · subst x
              simp [heta]
            · rw [setClosed_of_ne hx]
          rw [hclose]
          by_cases hA : setOpen e eta ∈ A <;>
            simp [Set.indicator, hA]
      · apply Finset.sum_bij (fun omega _ => setClosed e omega)
        · intro omega homega
          simp
        · intro omega homega rho hrho heq
          funext x
          by_cases hx : x = e
          · subst x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Bool.not_eq_false] at homega hrho
            rw [homega, hrho]
          · have hxval := congrFun heq x
            simpa [setClosed_of_ne hx] using hxval
        · intro eta heta
          refine ⟨setOpen e eta, by simp, ?_⟩
          funext x
          by_cases hx : x = e
          · subst x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
            simp [heta]
          · rw [setClosed_of_ne hx, setOpen_of_ne hx]
        · intro omega homega
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Bool.not_eq_false] at homega
          have hopen : setOpen e omega = omega := by
            funext x
            by_cases hx : x = e
            · subst x
              simp [homega]
            · rw [setOpen_of_ne hx]
          have hopenClosed : setOpen e (setClosed e omega) = omega := by
            funext x
            by_cases hx : x = e
            · subst x
              simp [homega]
            · rw [setOpen_of_ne hx, setClosed_of_ne hx]
          rw [hopenClosed]
          by_cases hA : omega ∈ A <;>
            simp [Set.indicator, hA, hopen]
    _ = ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E =>
          eta e = false),
        A.indicator (fun _ => mu (setOpen e eta) + mu (setClosed e eta))
          (setOpen e eta) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro eta heta
      by_cases hA : setOpen e eta ∈ A <;> simp [hA, add_comm]

theorem finiteBoolClosedEventSum_le
    (mu : ConfigSpace E → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (e : E) (A : Set (ConfigSpace E)) :
    (∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E => eta e = false),
        A.indicator (fun _ => mu (setClosed e eta)) (setClosed e eta)) ≤
      finiteBoolEventMass mu A := by
  classical
  unfold finiteBoolEventMass
  calc
    _ = ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E => eta e = false),
        A.indicator mu eta := by
      apply Finset.sum_congr rfl
      intro eta heta
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
      have hclose : setClosed e eta = eta := by
        funext x
        by_cases hx : x = e
        · subst x
          simp [heta]
        · rw [setClosed_of_ne hx]
      rw [hclose]
      by_cases hA : eta ∈ A <;> simp [hA]
    _ ≤ ∑ eta ∈ (Finset.univ : Finset (ConfigSpace E)),
        A.indicator mu eta := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro eta heta hnot
      exact Set.indicator_nonneg (fun _ _ => hmu _) _

theorem finiteBoolOpenEventSum_le
    (mu : ConfigSpace E → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (e : E) (A : Set (ConfigSpace E)) :
    (∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E => eta e = false),
        A.indicator (fun _ => mu (setOpen e eta)) (setOpen e eta)) ≤
      finiteBoolEventMass mu A := by
  classical
  unfold finiteBoolEventMass
  calc
    _ = ∑ omega ∈ (Finset.univ.filter fun omega : ConfigSpace E =>
          omega e = true), A.indicator mu omega := by
      apply Finset.sum_bij (fun eta _ => setOpen e eta)
      · intro eta heta
        simp
      · intro eta heta rho hrho heq
        funext x
        by_cases hx : x = e
        · subst x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta hrho
          rw [heta, hrho]
        · have hxval := congrFun heq x
          simpa [setOpen_of_ne hx] using hxval
      · intro omega homega
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega
        refine ⟨setClosed e omega, by simp, ?_⟩
        funext x
        by_cases hx : x = e
        · subst x
          simp [homega]
        · rw [setOpen_of_ne hx, setClosed_of_ne hx]
      · intro eta heta
        by_cases hA : setOpen e eta ∈ A <;> simp [hA]
    _ ≤ ∑ omega ∈ (Finset.univ : Finset (ConfigSpace E)),
        A.indicator mu omega := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro omega homega hnot
      exact Set.indicator_nonneg (fun _ _ => hmu _) _

theorem finiteBool_c_mul_preimage_setClosed_le_event
    (mu : ConfigSpace E → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (c : Real)
    (hpair : ∀ e eta, c * (mu (setOpen e eta) + mu (setClosed e eta)) ≤
      mu (setClosed e eta)) (e : E) (A : Set (ConfigSpace E)) :
    c * finiteBoolEventMass mu (setClosed e ⁻¹' A) ≤
      finiteBoolEventMass mu A := by
  rw [finiteBoolEventMass_preimage_setClosed]
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E => eta e = false),
        A.indicator (fun _ => mu (setClosed e eta)) (setClosed e eta) := by
      apply Finset.sum_le_sum
      intro eta heta
      by_cases hA : setClosed e eta ∈ A
      · simp only [Set.indicator_of_mem hA]
        exact hpair e eta
      · simp [Set.indicator_of_notMem hA]
    _ ≤ finiteBoolEventMass mu A :=
      finiteBoolClosedEventSum_le mu hmu e A

theorem finiteBool_c_mul_preimage_setOpen_le_event
    (mu : ConfigSpace E → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (c : Real)
    (hpair : ∀ e eta, c * (mu (setOpen e eta) + mu (setClosed e eta)) ≤
      mu (setOpen e eta)) (e : E) (A : Set (ConfigSpace E)) :
    c * finiteBoolEventMass mu (setOpen e ⁻¹' A) ≤
      finiteBoolEventMass mu A := by
  rw [finiteBoolEventMass_preimage_setOpen]
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ eta ∈ (Finset.univ.filter fun eta : ConfigSpace E => eta e = false),
        A.indicator (fun _ => mu (setOpen e eta)) (setOpen e eta) := by
      apply Finset.sum_le_sum
      intro eta heta
      by_cases hA : setOpen e eta ∈ A
      · simp only [Set.indicator_of_mem hA]
        exact hpair e eta
      · simp [Set.indicator_of_notMem hA]
    _ ≤ finiteBoolEventMass mu A :=
      finiteBoolOpenEventSum_le mu hmu e A

theorem finiteBool_c_pow_mul_forceClosed_preimage_le_event
    (mu : ConfigSpace E → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (c : Real) (hc : 0 ≤ c)
    (hpair : ∀ e eta, c * (mu (setOpen e eta) + mu (setClosed e eta)) ≤
      mu (setClosed e eta)) (I : Finset E) (A : Set (ConfigSpace E)) :
    c ^ I.card * finiteBoolEventMass mu (finiteBoolForceClosed I ⁻¹' A) ≤
      finiteBoolEventMass mu A := by
  classical
  induction I using Finset.induction with
  | empty =>
      have hpre : finiteBoolForceClosed ∅ ⁻¹' A = A := by
        ext omega
        simp only [Set.mem_preimage]
        rw [finiteBoolForceClosed_empty]
      rw [Finset.card_empty, pow_zero, one_mul, hpre]
  | @insert e I he ih =>
      rw [Finset.card_insert_of_notMem he, pow_succ]
      have hpre : finiteBoolForceClosed (insert e I) ⁻¹' A =
          setClosed e ⁻¹' (finiteBoolForceClosed I ⁻¹' A) := by
        ext omega
        simp only [Set.mem_preimage]
        rw [finiteBoolForceClosed_insert]
      rw [hpre]
      calc
        _ = c ^ I.card *
            (c * finiteBoolEventMass mu
              (setClosed e ⁻¹' (finiteBoolForceClosed I ⁻¹' A))) := by ring
        _ ≤ c ^ I.card * finiteBoolEventMass mu
              (finiteBoolForceClosed I ⁻¹' A) :=
          mul_le_mul_of_nonneg_left
            (finiteBool_c_mul_preimage_setClosed_le_event
              mu hmu c hpair e _) (pow_nonneg hc _)
        _ ≤ finiteBoolEventMass mu A := ih

theorem finiteBool_c_pow_mul_forceOpen_preimage_le_event
    (mu : ConfigSpace E → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (c : Real) (hc : 0 ≤ c)
    (hpair : ∀ e eta, c * (mu (setOpen e eta) + mu (setClosed e eta)) ≤
      mu (setOpen e eta)) (I : Finset E) (A : Set (ConfigSpace E)) :
    c ^ I.card * finiteBoolEventMass mu (finiteBoolForceOpen I ⁻¹' A) ≤
      finiteBoolEventMass mu A := by
  classical
  induction I using Finset.induction with
  | empty =>
      have hpre : finiteBoolForceOpen ∅ ⁻¹' A = A := by
        ext omega
        simp only [Set.mem_preimage]
        rw [finiteBoolForceOpen_empty]
      rw [Finset.card_empty, pow_zero, one_mul, hpre]
  | @insert e I he ih =>
      rw [Finset.card_insert_of_notMem he, pow_succ]
      have hpre : finiteBoolForceOpen (insert e I) ⁻¹' A =
          setOpen e ⁻¹' (finiteBoolForceOpen I ⁻¹' A) := by
        ext omega
        simp only [Set.mem_preimage]
        rw [finiteBoolForceOpen_insert]
      rw [hpre]
      calc
        _ = c ^ I.card *
            (c * finiteBoolEventMass mu
              (setOpen e ⁻¹' (finiteBoolForceOpen I ⁻¹' A))) := by ring
        _ ≤ c ^ I.card * finiteBoolEventMass mu
              (finiteBoolForceOpen I ⁻¹' A) :=
          mul_le_mul_of_nonneg_left
            (finiteBool_c_mul_preimage_setOpen_le_event
              mu hmu c hpair e _) (pow_nonneg hc _)
        _ ≤ finiteBoolEventMass mu A := ih

end FiniteBoolPushforward


theorem fkRectGraphCritical_cFE_mul_preimage_setClosed_le_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (A : Set (FKRectGraphConfiguration R)) :
    FK.cFE (fkRectCriticalP q) q *
        fkRectGraphCriticalEventMass R q (setClosed e ⁻¹' A) ≤
      fkRectGraphCriticalEventMass R q A := by
  exact finiteBool_c_mul_preimage_setClosed_le_event
    (fun eta => fkRectGraphCriticalRandomClusterProb R q eta)
    (fun eta => fkRectGraphCriticalRandomClusterProb_nonneg R
      (lt_of_lt_of_le zero_lt_one hq) eta)
    (FK.cFE (fkRectCriticalP q) q)
    (fkRectGraphCriticalProb_setClosed_ge R hq) e A


theorem fkRectGraphCritical_cFE_pow_mul_forceClosed_preimage_le_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (A : Set (FKRectGraphConfiguration R)) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectGraphCriticalEventMass R q
          (fkRectGraphForceClosed R I ⁻¹' A) ≤
      fkRectGraphCriticalEventMass R q A := by
  simpa [fkRectGraphCriticalEventMass, fkRectGraphForceClosed,
    finiteBoolEventMass, finiteBoolForceClosed] using
    finiteBool_c_pow_mul_forceClosed_preimage_le_event
      (fun eta => fkRectGraphCriticalRandomClusterProb R q eta)
      (fun eta => fkRectGraphCriticalRandomClusterProb_nonneg R
        (lt_of_lt_of_le zero_lt_one hq) eta)
      (FK.cFE (fkRectCriticalP q) q) (fkRectCritical_cFE_nonneg hq)
      (fkRectGraphCriticalProb_setClosed_ge R hq) I A


end
end StatMech.FrontierD
