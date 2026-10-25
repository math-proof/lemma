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
import Def.StatisticalMechanics.Code.Walls.gc92borbitobstruction
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


theorem gc92b_no_equivariant_injection (ends : ι → Sym2 W) (τ : Equiv.Perm ι) (m : Finset ι)
    {o x y g : W}
    {s₁ s₂ : Finset ι × Finset ι}
    (hs₁ : s₁ ∈ gc91b_cogxgPairs ends m o x g) (hs₂ : s₂ ∈ gc91b_cogxgPairs ends m o x g)
    (hswap : s₂ = gc92b_pairAction τ s₁) (hne : s₁ ≠ s₂)
    (hT3fixed : ∀ t ∈ gc91b_T3Pairs ends m o x y g, gc92b_pairAction τ t = t)
    (f : Finset ι × Finset ι → Finset ι × Finset ι)
    (hmaps : ∀ s ∈ gc91b_cogxgPairs ends m o x g, f s ∈ gc91b_T3Pairs ends m o x y g)
    (hequiv : f (gc92b_pairAction τ s₁) = gc92b_pairAction τ (f s₁))
    (hinj : Set.InjOn f (gc91b_cogxgPairs ends m o x g)) : False := by
  have h1 : f s₂ = gc92b_pairAction τ (f s₁) := by rw [hswap]; exact hequiv
  have h2 : gc92b_pairAction τ (f s₁) = f s₁ := hT3fixed (f s₁) (hmaps s₁ hs₁)
  have h3 : f s₂ = f s₁ := h1.trans h2
  exact hne ((hinj hs₁ hs₂ h3.symm))


theorem gc92b_wred_perm_fixes : ∀ i : Fin 4,
    gc88b_wredEnds (Equiv.swap (1 : Fin 4) 2 i) = gc88b_wredEnds i := by
  decide


theorem gc92b_wred_perm_fixes_univ :
    (univ : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = univ := by
  decide


theorem gc92b_wred_swap_cogxg :
    ({1} : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = ({2} : Finset (Fin 4))
      ∧ ({2} : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = ({1} : Finset (Fin 4))
      ∧ (∅ : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = (∅ : Finset (Fin 4)) := by
  refine ⟨by decide, by decide, by decide⟩


theorem gc92b_wred_swap_fixes_T3 :
    gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) ((∅ : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        = ((∅ : Finset (Fin 4)), (∅ : Finset (Fin 4)))
      ∧ gc92b_pairAction (Equiv.swap (1 : Fin 4) 2)
          ((∅ : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)))
        = ((∅ : Finset (Fin 4)), ({1, 2} : Finset (Fin 4))) := by
  refine ⟨by decide, by decide⟩


theorem gc92b_wred_mem_cogxg_one :
    (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
      ∈ gc91b_cogxgPairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 3 := by
  unfold gc91b_cogxgPairs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  refine ⟨⟨Finset.subset_univ _, Finset.subset_univ _⟩, by decide, by decide, by decide, ?_⟩
  refine Relation.ReflTransGen.head (b := (0 : Fin 4)) ⟨0, by decide, by decide, by decide, by decide⟩
    (Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩)


theorem gc92b_wred_mem_cogxg_two :
    (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
      ∈ gc91b_cogxgPairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 3 := by
  unfold gc91b_cogxgPairs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  refine ⟨⟨Finset.subset_univ _, Finset.subset_univ _⟩, by decide, by decide, by decide, ?_⟩
  refine Relation.ReflTransGen.head (b := (0 : Fin 4)) ⟨0, by decide, by decide, by decide, by decide⟩
    (Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩)


theorem gc92b_wred_cogxg_swapped :
    (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        ≠ (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
      ∧ gc92b_pairAction (Equiv.swap (1 : Fin 4) 2)
          (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        = (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4))) := by
  refine ⟨by decide, by decide⟩


theorem gc92b_wred_no_equivariant_injection
    (hT3fixed : ∀ t ∈ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3,
        gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) t = t)
    (f : Finset (Fin 4) × Finset (Fin 4) → Finset (Fin 4) × Finset (Fin 4))
    (hmaps : ∀ s ∈ gc91b_cogxgPairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 3,
        f s ∈ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3)
    (hequiv : f (gc92b_pairAction (Equiv.swap (1 : Fin 4) 2)
          (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))))
        = gc92b_pairAction (Equiv.swap (1 : Fin 4) 2)
          (f (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))))
    (hinj : Set.InjOn f (gc91b_cogxgPairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 3)) :
    False := by
  refine gc92b_no_equivariant_injection gc88b_wredEnds (Equiv.swap (1 : Fin 4) 2)
    (univ : Finset (Fin 4)) (o := 0) (x := 1) (y := 2) (g := 3)
    gc92b_wred_mem_cogxg_one gc92b_wred_mem_cogxg_two
    gc92b_wred_cogxg_swapped.2.symm gc92b_wred_cogxg_swapped.1
    hT3fixed f hmaps hequiv hinj


theorem gc92b_orbit_status (ends : ι → Sym2 W) (τ : Equiv.Perm ι) (m : Finset ι)
    (hτ : ∀ i, ends (τ i) = ends i) (hm : m.image τ = m) {o x y g : W}
    {s₁ s₂ : Finset ι × Finset ι}
    (hs₁ : s₁ ∈ gc91b_cogxgPairs ends m o x g) (hs₂ : s₂ ∈ gc91b_cogxgPairs ends m o x g)
    (hswap : s₂ = gc92b_pairAction τ s₁) (hne : s₁ ≠ s₂)
    (hT3fixed : ∀ t ∈ gc91b_T3Pairs ends m o x y g, gc92b_pairAction τ t = t) :
    
    (∀ K₁ K₂, (K₁.image τ, K₂.image τ) ∈ gc91b_cogxgPairs ends m o x g
        ↔ (K₁, K₂) ∈ gc91b_cogxgPairs ends m o x g)
    ∧ (∀ J₁ J₂, (J₁.image τ, J₂.image τ) ∈ gc91b_T3Pairs ends m o x y g
        ↔ (J₁, J₂) ∈ gc91b_T3Pairs ends m o x y g)
    
    ∧ (∀ f : Finset ι × Finset ι → Finset ι × Finset ι,
        (∀ s ∈ gc91b_cogxgPairs ends m o x g, f s ∈ gc91b_T3Pairs ends m o x y g) →
        f (gc92b_pairAction τ s₁) = gc92b_pairAction τ (f s₁) →
        Set.InjOn f (gc91b_cogxgPairs ends m o x g) → False) := by
  refine ⟨fun K₁ K₂ => gc92b_perm_mem_cogxgSet_iff ends τ hτ m hm o x g K₁ K₂,
      fun J₁ J₂ => gc92b_perm_mem_T3Set_iff ends τ hτ m hm o x y g J₁ J₂, ?_⟩
  intro f hmaps hequiv hinj
  exact gc92b_no_equivariant_injection ends τ m hs₁ hs₂ hswap hne hT3fixed f hmaps hequiv hinj


theorem gc92b_machine_findings : True := trivial

end StatMech.Walls
