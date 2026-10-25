/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part6
import Def.StatisticalMechanics.Code.Walls.rc79toporbit.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc79_colTypeF_diag_iff (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    rc78_colTypeF p = rc79_diagTypeF p.1 ↔ p.1 = p.2 := by
  unfold rc78_colTypeF rc79_diagTypeF
  rw [funext_iff]
  constructor
  · intro h; funext i
    have := h i
    rw [Prod.mk.injEq] at this
    
    obtain ⟨h1, h2⟩ := this
    cases hp1 : p.1 i <;> cases hp2 : p.2 i <;> simp_all
  · intro h i
    rw [h]
    cases (p.2 i) <;> simp


theorem rc79_occ_self_mem {A : Finset (ConfigSpace (Fin 2))} {K : Finset (Fin 2)}
    {w : ConfigSpace (Fin 2)} (h : rc75_occ A K w = true) : w ∈ A := by
  unfold rc75_occ at h
  rw [decide_eq_true_eq] at h
  exact h w (fun e _ => rfl)


theorem rc79_disjOcc_mem_both {A B : Finset (ConfigSpace (Fin 2))} {w : ConfigSpace (Fin 2)}
    (h : w ∈ rc75_disjOccF A B) : w ∈ A ∧ w ∈ B := by
  unfold rc75_disjOccF at h
  rw [Finset.mem_filter] at h
  obtain ⟨_, K, L, _, hA, hB⟩ := h
  exact ⟨rc79_occ_self_mem hA, rc79_occ_self_mem hB⟩


theorem rc79_diag_orbit_dominates (A B : Finset (ConfigSpace (Fin 2))) (w : ConfigSpace (Fin 2)) :
    rc78_srcOrbit A B (rc79_diagTypeF w) ⊆ rc78_tgtOrbit A B (rc79_diagTypeF w) := by
  intro p hp
  rw [rc78_srcOrbit, Finset.mem_filter] at hp
  obtain ⟨hpsrc, hptype⟩ := hp
  
  rw [rc75_sourceF, Finset.mem_product] at hpsrc
  obtain ⟨hp1, _⟩ := hpsrc
  
  
  have hdiag_p1 : rc78_colTypeF p = rc79_diagTypeF p.1 := by
    funext i
    have := congrArg (fun f => f i) hptype
    
    simp only [rc79_diagTypeF] at this ⊢
    unfold rc78_colTypeF at this ⊢
    
    rw [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    cases hp1' : p.1 i <;> cases hp2' : p.2 i <;> simp_all
  have hp1eqp2 : p.1 = p.2 := (rc79_colTypeF_diag_iff p).mp hdiag_p1
  
  obtain ⟨hA, hB⟩ := rc79_disjOcc_mem_both hp1
  rw [rc78_tgtOrbit, Finset.mem_filter]
  refine ⟨?_, hptype⟩
  rw [rc75_prodF, Finset.mem_product]
  exact ⟨hA, by rw [← hp1eqp2]; exact hB⟩


theorem rc79_diag_orbit_card_le (A B : Finset (ConfigSpace (Fin 2))) (w : ConfigSpace (Fin 2)) :
    (rc78_srcOrbit A B (rc79_diagTypeF w)).card ≤ (rc78_tgtOrbit A B (rc79_diagTypeF w)).card :=
  Finset.card_le_card (rc79_diag_orbit_dominates A B w)


end StatMech.Walls
