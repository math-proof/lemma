/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc92borbitobstruction.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.gc86brerouteinjection.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc87brerouteinjection.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc88brereroutehall.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc89bmetricinjection.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc90bperfiberinject.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc91bglobalinjection
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


theorem gc92b_degK_perm (ends : ι → Sym2 W) (τ : Equiv.Perm ι) (hτ : ∀ i, ends (τ i) = ends i)
    (K : Finset ι) (w : W) : degK ends (K.image τ) w = degK ends K w := by
  unfold degK
  rw [Finset.filter_image, Finset.card_image_of_injective _ τ.injective]
  congr 1
  ext i
  simp only [Finset.mem_filter, hτ]


theorem gc92b_sources_perm (ends : ι → Sym2 W) (τ : Equiv.Perm ι) (hτ : ∀ i, ends (τ i) = ends i)
    (K : Finset ι) : sources ends (K.image τ) = sources ends K := by
  ext w
  simp only [RandomCurrent.mem_sources, gc92b_degK_perm ends τ hτ K w]


theorem gc92b_adjStep_perm (ends : ι → Sym2 W) (τ : Equiv.Perm ι) (hτ : ∀ i, ends (τ i) = ends i)
    (K : Finset ι) (a b : W) : adjStep ends (K.image τ) a b ↔ adjStep ends K a b := by
  unfold adjStep
  constructor
  · rintro ⟨i, hi, ha, hb, hne⟩
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact ⟨j, hj, by rwa [hτ] at ha, by rwa [hτ] at hb, hne⟩
  · rintro ⟨i, hi, ha, hb, hne⟩
    refine ⟨τ i, Finset.mem_image_of_mem τ hi, ?_, ?_, hne⟩
    · rwa [hτ]
    · rwa [hτ]


theorem gc92b_connK_perm (ends : ι → Sym2 W) (τ : Equiv.Perm ι) (hτ : ∀ i, ends (τ i) = ends i)
    (K : Finset ι) (a b : W) : connK ends (K.image τ) a b ↔ connK ends K a b := by
  unfold connK
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.tail ih ((gc92b_adjStep_perm ends τ hτ K _ _).1 hstep)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.tail ih ((gc92b_adjStep_perm ends τ hτ K _ _).2 hstep)


theorem gc92b_image_sdiff (τ : Equiv.Perm ι) (m K : Finset ι) (hm : m.image τ = m) :
    (m \ K).image τ = m \ (K.image τ) := by
  rw [Finset.image_sdiff _ _ τ.injective, hm]


theorem gc92b_connK_complement_perm (ends : ι → Sym2 W) (τ : Equiv.Perm ι)
    (hτ : ∀ i, ends (τ i) = ends i) (m K : Finset ι) (hm : m.image τ = m) (a b : W) :
    connK ends (m \ (K.image τ)) a b ↔ connK ends (m \ K) a b := by
  rw [← gc92b_image_sdiff τ m K hm, gc92b_connK_perm ends τ hτ]


theorem gc92b_perm_mem_cogxgSet_iff (ends : ι → Sym2 W) (τ : Equiv.Perm ι)
    (hτ : ∀ i, ends (τ i) = ends i) (m : Finset ι) (hm : m.image τ = m) (o x g : W)
    (K₁ K₂ : Finset ι) :
    (K₁.image τ, K₂.image τ) ∈ gc91b_cogxgPairs ends m o x g
      ↔ (K₁, K₂) ∈ gc91b_cogxgPairs ends m o x g := by
  unfold gc91b_cogxgPairs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  rw [gc92b_sources_perm ends τ hτ, gc92b_sources_perm ends τ hτ,
      gc92b_connK_complement_perm ends τ hτ m K₁ hm]
  have hmem : ∀ a : ι, a ∈ m ↔ τ a ∈ m := by
    intro a; conv_rhs => rw [← hm]
    rw [Finset.mem_image]
    exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, hba⟩ => by rwa [← τ.injective hba]⟩
  constructor
  · rintro ⟨⟨h1, h2⟩, hdis, hs1, hs2, hc⟩
    refine ⟨⟨?_, ?_⟩, ?_, hs1, hs2, hc⟩
    · intro a ha; rw [hmem]; exact h1 (Finset.mem_image_of_mem τ ha)
    · intro a ha; rw [hmem]; exact h2 (Finset.mem_image_of_mem τ ha)
    · rw [Finset.disjoint_left] at hdis ⊢
      intro a haK haK2
      exact hdis (Finset.mem_image_of_mem τ haK) (Finset.mem_image_of_mem τ haK2)
  · rintro ⟨⟨h1, h2⟩, hdis, hs1, hs2, hc⟩
    refine ⟨⟨?_, ?_⟩, ?_, hs1, hs2, hc⟩
    · rw [← hm]; exact Finset.image_subset_image h1
    · rw [← hm]; exact Finset.image_subset_image h2
    · rw [Finset.disjoint_left] at hdis ⊢
      intro a haK haK2
      rw [Finset.mem_image] at haK haK2
      obtain ⟨i, hi, rfl⟩ := haK
      obtain ⟨j, hj, hij⟩ := haK2
      rw [τ.injective hij] at hj
      exact hdis hi hj


theorem gc92b_perm_mem_T3Set_iff (ends : ι → Sym2 W) (τ : Equiv.Perm ι)
    (hτ : ∀ i, ends (τ i) = ends i) (m : Finset ι) (hm : m.image τ = m) (o x y g : W)
    (J₁ J₂ : Finset ι) :
    (J₁.image τ, J₂.image τ) ∈ gc91b_T3Pairs ends m o x y g
      ↔ (J₁, J₂) ∈ gc91b_T3Pairs ends m o x y g := by
  unfold gc91b_T3Pairs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  rw [gc92b_sources_perm ends τ hτ, gc92b_sources_perm ends τ hτ,
      gc92b_connK_complement_perm ends τ hτ m J₁ hm,
      gc92b_connK_complement_perm ends τ hτ m J₁ hm,
      gc92b_connK_complement_perm ends τ hτ m J₁ hm]
  have hmem : ∀ a : ι, a ∈ m ↔ τ a ∈ m := by
    intro a; conv_rhs => rw [← hm]
    rw [Finset.mem_image]
    exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, hba⟩ => by rwa [← τ.injective hba]⟩
  constructor
  · rintro ⟨⟨h1, h2⟩, hdis, hs1, hs2, hc1, hc2, hc3⟩
    refine ⟨⟨?_, ?_⟩, ?_, hs1, hs2, hc1, hc2, hc3⟩
    · intro a ha; rw [hmem]; exact h1 (Finset.mem_image_of_mem τ ha)
    · intro a ha; rw [hmem]; exact h2 (Finset.mem_image_of_mem τ ha)
    · rw [Finset.disjoint_left] at hdis ⊢
      intro a haK haK2
      exact hdis (Finset.mem_image_of_mem τ haK) (Finset.mem_image_of_mem τ haK2)
  · rintro ⟨⟨h1, h2⟩, hdis, hs1, hs2, hc1, hc2, hc3⟩
    refine ⟨⟨?_, ?_⟩, ?_, hs1, hs2, hc1, hc2, hc3⟩
    · rw [← hm]; exact Finset.image_subset_image h1
    · rw [← hm]; exact Finset.image_subset_image h2
    · rw [Finset.disjoint_left] at hdis ⊢
      intro a haK haK2
      rw [Finset.mem_image] at haK haK2
      obtain ⟨i, hi, rfl⟩ := haK
      obtain ⟨j, hj, hij⟩ := haK2
      rw [τ.injective hij] at hj
      exact hdis hi hj


end StatMech.Walls
