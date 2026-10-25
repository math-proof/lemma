/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
import Def.StatisticalMechanics.Code.Walls.gc86brerouteinjection
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


theorem gc86b_ncount_conn_eq (ends : ι → Sym2 W) (R : Finset ι) {u v : W} (huv : u ≠ v)
    (hconn : connK ends R u v) :
    gc86b_ncount ends R {u, v} = gc86b_ncount ends R ∅ := by
  unfold gc86b_ncount
  obtain ⟨P, hPm, hPsrc⟩ := exists_conn_set ends R hconn huv
  have hbij := sources_shift_bijOn ends R P hPm (∅ : Finset W)
  rw [hPsrc, show (∅ : Finset W) = ⊥ from rfl, bot_symmDiff] at hbij
  
  have himg : (R.powerset.filter (fun K => sources ends K = ({u, v} : Finset W)))
      = (R.powerset.filter (fun K => sources ends K = ∅)).image (fun K => K ∆ P) := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · intro ⟨hKm, hKsrc⟩
      obtain ⟨L, hL, hLK⟩ := hbij.2.2 ⟨hKm, hKsrc⟩
      exact ⟨L, ⟨hL.1, hL.2⟩, hLK⟩
    · rintro ⟨L, ⟨hLm, hLsrc⟩, rfl⟩
      have := hbij.1 ⟨hLm, hLsrc⟩
      exact ⟨this.1, this.2⟩
  rw [himg, Finset.card_image_of_injOn]
  intro K₁ hK₁ K₂ hK₂ h
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hK₁ hK₂
  exact hbij.2.1 ⟨hK₁.1, hK₁.2⟩ ⟨hK₂.1, hK₂.2⟩ h


theorem gc86b_strong_of_conn (ends : ι → Sym2 W) (R : Finset ι)
    (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends R = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    gc86b_ncount ends R ∅
      ≤ gc86b_ncount ends R {o, x} + gc86b_ncount ends R {o, y} + gc86b_ncount ends R {o, g} := by
  rcases gc86b_o_connects_mark ends R hnd hsrc hox hoy hog with h | h | h
  · 
    have he := gc86b_ncount_conn_eq ends R hox h
    omega
  · 
    have he := gc86b_ncount_conn_eq ends R hoy h
    omega
  · 
    have he := gc86b_ncount_conn_eq ends R hog h
    omega


theorem gc85b_pcount_fiber (ends : ι → Sym2 W) (m : Finset ι) (A B : Finset W) :
    gc85b_pcount ends m A B
      = ∑ K₁ ∈ m.powerset.filter (fun K => sources ends K = A),
          gc86b_ncount ends (m \ K₁) B := by
  unfold gc85b_pcount gc86b_ncount
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun KK => KK.1)
        (t := m.powerset.filter (fun K => sources ends K = A))
        (s := (m.powerset ×ˢ m.powerset).filter
          (fun KK => Disjoint KK.1 KK.2 ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B))
        (fun KK hKK => by
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hKK
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨hKK.1.1, hKK.2.2.1⟩)]
  refine Finset.sum_congr rfl (fun K₁ hK₁ => ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset] at hK₁
  
  symm
  apply Finset.card_bij (fun K₂ _ => (K₁, K₂))
  · intro K₂ hK₂
    simp only [Finset.mem_filter, Finset.mem_powerset] at hK₂
    obtain ⟨hK₂sub, hK₂src⟩ := hK₂
    have hK₂m : K₂ ⊆ m := hK₂sub.trans (Finset.sdiff_subset)
    have hdis : Disjoint K₁ K₂ := by
      rw [Finset.disjoint_left]
      intro a haK₁ haK₂
      exact (Finset.mem_sdiff.1 (hK₂sub haK₂)).2 haK₁
    rw [Finset.mem_filter]
    refine ⟨?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨Finset.mem_powerset.2 hK₁.1, Finset.mem_powerset.2 hK₂m⟩, hdis, hK₁.2, hK₂src⟩
  · intro K₂ hK₂ K₂' hK₂' h
    simp only [Prod.mk.injEq] at h
    exact h.2
  · rintro ⟨L₁, L₂⟩ hLL
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hLL
    obtain ⟨⟨⟨hL₁m, hL₂m⟩, hdis, hL₁src, hL₂src⟩, hproj⟩ := hLL
    subst hproj
    refine ⟨L₂, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, hL₂src⟩
    intro a ha
    rw [Finset.mem_sdiff]
    exact ⟨hL₂m ha, fun hK₁ => (Finset.disjoint_left.1 hdis) hK₁ ha⟩


theorem gc86b_sources_sdiff_of_empty (ends : ι → Sym2 W) {m K₁ : Finset ι} (hK₁m : K₁ ⊆ m)
    (hK₁ : sources ends K₁ = ∅) :
    sources ends (m \ K₁) = sources ends m := by
  have hsd : m \ K₁ = m ∆ K₁ := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff]
    constructor
    · rintro ⟨ham, haK₁⟩; exact Or.inl ⟨ham, haK₁⟩
    · rintro (⟨ham, haK₁⟩ | ⟨haK₁, ham⟩)
      · exact ⟨ham, haK₁⟩
      · exact absurd (hK₁m haK₁) ham
  rw [hsd, sources_symmDiff, hK₁, show (∅ : Finset W) = ⊥ from rfl, symmDiff_bot]


theorem gc86b_strong_global (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    gc85b_pcount ends m ∅ ∅
      ≤ gc85b_pcount ends m ∅ {o, g} + gc85b_pcount ends m ∅ {o, x} + gc85b_pcount ends m ∅ {o, y} := by
  rw [gc85b_pcount_fiber ends m ∅ ∅, gc85b_pcount_fiber ends m ∅ {o, g},
      gc85b_pcount_fiber ends m ∅ {o, x}, gc85b_pcount_fiber ends m ∅ {o, y},
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun K₁ hK₁ => ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset] at hK₁
  obtain ⟨hK₁m, hK₁src⟩ := hK₁
  
  have hRsrc : sources ends (m \ K₁) = ({o, x, y, g} : Finset W) := by
    rw [gc86b_sources_sdiff_of_empty ends hK₁m hK₁src, hsrc]
  have hRnd : ∀ i ∈ m \ K₁, ¬ (ends i).IsDiag := fun i hi => hnd i (Finset.mem_sdiff.1 hi).1
  
  have hstrong := gc86b_strong_of_conn ends (m \ K₁) hRnd hRsrc hox hoy hog
  
  omega


end StatMech.Walls
