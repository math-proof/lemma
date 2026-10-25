/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneDual.Part3
import Theorem.StatisticalMechanics.Code.Walls.rb3reimerclose.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc4_core
import Theorem.StatisticalMechanics.Code.Walls.rc3_keyflipinvolutive
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.ConfigSpace

open StatMech.Walls

open StatMech.Walls.Reimer

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem kssWeightInjection_fin {n : ℕ}
    (A B : Set (ConfigSpace (Fin n))) : KSSWeightInjection A B := by
  classical
  set Dom := {p : ConfigSpace (Fin n) × ConfigSpace (Fin n) //
    p ∈ dualDisjointOccurrence A B} with hDom
  set r : Dom → (ConfigSpace (Fin n) × ConfigSpace (Fin n)) → Prop :=
    fun p q => sameOrbit p.val q ∧ q.1 ∈ A ∩ B with hr
  have key : ∃ f : Dom → (ConfigSpace (Fin n) × ConfigSpace (Fin n)),
      Function.Injective f ∧ ∀ x, r x (f x) := by
    rw [← Fintype.all_card_le_filter_rel_iff_exists_injective r]
    intro S
    set K := S.image (fun p : Dom => orbitKey p.val) with hK
    have hfib : #S = ∑ k ∈ K, #(S.filter (fun p => orbitKey p.val = k)) := by
      apply Finset.card_eq_sum_card_fiberwise
      intro p hp
      exact Finset.mem_image_of_mem _ hp
    rw [hfib]
    have hkstep : ∀ k ∈ K,
        #(S.filter (fun p => orbitKey p.val = k)) ≤
          #(kssDiagonalOrbit A B k) := by
      intro k _
      refine le_trans ?_ (kssDualOrbit_card_le A B k)
      apply Finset.card_le_card_of_injOn (fun p => p.val)
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        rw [Finset.mem_coe, kssDualOrbit, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, p.property, hp.2⟩
      · intro p _ q _ hpq
        exact Subtype.ext hpq
    calc
      ∑ k ∈ K, #(S.filter (fun p => orbitKey p.val = k))
          ≤ ∑ k ∈ K, #(kssDiagonalOrbit A B k) :=
        Finset.sum_le_sum hkstep
      _ = #(K.biUnion fun k => kssDiagonalOrbit A B k) := by
        rw [Finset.card_biUnion]
        intro k1 _ k2 _ hne
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro q hq1 hq2
        simp only [kssDiagonalOrbit, Finset.mem_filter] at hq1 hq2
        exact hne (hq1.2.2 ▸ hq2.2.2)
      _ ≤ #{q | ∃ p ∈ S, r p q} := by
        apply Finset.card_le_card
        intro q hq
        rw [Finset.mem_biUnion] at hq
        obtain ⟨k, hkK, hqdiag⟩ := hq
        simp only [kssDiagonalOrbit, Finset.mem_filter] at hqdiag
        rw [hK, Finset.mem_image] at hkK
        obtain ⟨p, hpS, hpk⟩ := hkK
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ q, p, hpS, ?_, hqdiag.2.1⟩
        rw [sameOrbit_iff_orbitKey, hpk, ← hqdiag.2.2]
  obtain ⟨f, hfinj, hfr⟩ := key
  let Phi : ConfigSpace (Fin n) × ConfigSpace (Fin n) →
      ConfigSpace (Fin n) × ConfigSpace (Fin n) := fun p =>
    if hp : p ∈ dualDisjointOccurrence A B then f ⟨p, hp⟩ else p
  refine ⟨Phi, ?_, ?_, ?_⟩
  · intro p hp
    simpa only [Phi, dif_pos hp] using (hfr ⟨p, hp⟩).2
  · intro phi p hp
    exact pairWeight_eq_of_sameOrbit phi
      (by simpa only [Phi, dif_pos hp] using (hfr ⟨p, hp⟩).1)
  · intro p hp q hq hpq
    simp only [Phi, dif_pos hp, dif_pos hq] at hpq
    exact Subtype.ext_iff.mp (hfinj hpq)


theorem dualBKR_wprob_fin {n : ℕ} (phi : Fin n → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (A B : Set (ConfigSpace (Fin n))) :
    dualWprob phi (dualDisjointOccurrence A B) ≤ wprob phi (A ∩ B) := by
  classical
  obtain ⟨Phi, hmem, hwt, hinj⟩ := kssWeightInjection_fin A B
  set D := dualDisjointOccurrence A B with hD
  set C := A ∩ B with hC
  set target := C ×ˢ (Set.univ : Set (ConfigSpace (Fin n))) with htarget
  set g : ConfigSpace (Fin n) × ConfigSpace (Fin n) → ℝ := fun p =>
    target.indicator (fun _ => (1 : ℝ)) p *
      (pweight phi p.1 * pweight phi p.2) with hg
  have hg0 : ∀ p, 0 ≤ g p := by
    intro p
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      (mul_nonneg (pweight_nonneg hphi0 _) (pweight_nonneg hphi0 _))
  have htargetprob : dualWprob phi target = wprob phi C := by
    rw [htarget, dualWprob_prod]
    have huniv : wprob phi (Set.univ : Set (ConfigSpace (Fin n))) = 1 := by
      simp only [wprob, Set.indicator_univ, one_mul]
      exact sum_pweight_eq_one hphi1
    rw [huniv, mul_one]
  rw [← htargetprob]
  have hlhs : dualWprob phi D =
      ∑ p : ConfigSpace (Fin n) × ConfigSpace (Fin n),
        D.indicator (fun _ => (1 : ℝ)) p *
          (pweight phi p.1 * pweight phi p.2) := by
    unfold dualWprob
    rw [Fintype.sum_prod_type]
  have hrhs : dualWprob phi target =
      ∑ p : ConfigSpace (Fin n) × ConfigSpace (Fin n), g p := by
    unfold dualWprob
    rw [Fintype.sum_prod_type]
  rw [hlhs, hrhs]
  set domainPairs := Finset.univ.filter
    (fun p : ConfigSpace (Fin n) × ConfigSpace (Fin n) => p ∈ D) with hdomain
  have hlhs' :
      (∑ p : ConfigSpace (Fin n) × ConfigSpace (Fin n),
        D.indicator (fun _ => (1 : ℝ)) p *
          (pweight phi p.1 * pweight phi p.2)) =
      ∑ p ∈ domainPairs, pweight phi p.1 * pweight phi p.2 := by
    rw [hdomain, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun p : ConfigSpace (Fin n) × ConfigSpace (Fin n) => p ∈ D)]
    have hz :
        (∑ p ∈ Finset.univ.filter
          (fun p : ConfigSpace (Fin n) × ConfigSpace (Fin n) => ¬p ∈ D),
          D.indicator (fun _ => (1 : ℝ)) p *
            (pweight phi p.1 * pweight phi p.2)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Set.indicator_of_notMem hp.2, zero_mul]
    rw [hz, add_zero]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Set.indicator_of_mem hp.2, one_mul]
  rw [hlhs']
  have hwp :
      (∑ p ∈ domainPairs, pweight phi p.1 * pweight phi p.2) =
        ∑ p ∈ domainPairs, g (Phi p) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hdomain, Finset.mem_filter] at hp
    have hpD : p ∈ D := hp.2
    have hpDual : p ∈ dualDisjointOccurrence A B := by simpa [hD] using hpD
    have hpC : (Phi p).1 ∈ C := by simpa [hC] using hmem p hpDual
    have hpTarget : Phi p ∈ target := by
      exact ⟨hpC, Set.mem_univ _⟩
    simp only [hg]
    rw [Set.indicator_of_mem hpTarget, one_mul, hwt phi p hpDual]
  rw [hwp]
  rw [← Finset.sum_image (g := Phi) (f := g)
    (by
      intro p hp q hq hpq
      rw [hdomain, Finset.mem_coe, Finset.mem_filter] at hp hq
      apply hinj hp.2 hq.2 hpq)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun p _ _ => hg0 p)


theorem dualWprob_inter_univ {n : ℕ} (phi : Fin n → Bool → ℝ)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (C : Set (ConfigSpace (Fin n))) :
    dualWprob phi (C ×ˢ (Set.univ : Set (ConfigSpace (Fin n)))) =
      wprob phi C := by
  rw [dualWprob_prod]
  have huniv : wprob phi (Set.univ : Set (ConfigSpace (Fin n))) = 1 := by
    simp only [wprob, Set.indicator_univ, one_mul]
    exact sum_pweight_eq_one hphi1
  rw [huniv, mul_one]


end StatMech.FrontierA
