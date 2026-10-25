/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part6
import Def.StatisticalMechanics.Code.Walls.rc79toporbit.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc79_colTypeF_top_iff (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    rc78_colTypeF p = rc79_topTypeF ↔ ∀ i, p.1 i ≠ p.2 i := by
  unfold rc78_colTypeF rc79_topTypeF
  rw [funext_iff]
  constructor
  · intro h i; exact (rc79_mixed_iff_ne (p.1 i) (p.2 i)).mp (h i)
  · intro h i; exact (rc79_mixed_iff_ne (p.1 i) (p.2 i)).mpr (h i)


theorem rc79_colTypeF_top_iff_compl (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    rc78_colTypeF p = rc79_topTypeF ↔ p.2 = rc79_complF p.1 := by
  rw [rc79_colTypeF_top_iff]
  constructor
  · intro h; funext i; unfold rc79_complF
    have := h i; cases hp1 : p.1 i <;> cases hp2 : p.2 i <;> simp_all
  · intro h i; rw [h]; unfold rc79_complF; cases (p.1 i) <;> simp


theorem rc79_srcOrbit_top_card (A B : Finset (ConfigSpace (Fin 2))) :
    (rc78_srcOrbit A B rc79_topTypeF).card = (rc75_disjOccF A B).card := by
  apply Finset.card_bij (fun p _ => p.1)
  · 
    intro p hp
    rw [rc78_srcOrbit, Finset.mem_filter, rc75_sourceF, Finset.mem_product] at hp
    exact hp.1.1
  · 
    intro p hp q hq h
    rw [rc78_srcOrbit, Finset.mem_filter] at hp hq
    have hp2 := (rc79_colTypeF_top_iff_compl p).mp hp.2
    have hq2 := (rc79_colTypeF_top_iff_compl q).mp hq.2
    apply Prod.ext h
    rw [hp2, hq2, h]
  · 
    intro w hw
    refine ⟨(w, rc79_complF w), ?_, rfl⟩
    rw [rc78_srcOrbit, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [rc75_sourceF, Finset.mem_product]; exact ⟨hw, Finset.mem_univ _⟩
    · rw [rc79_colTypeF_top_iff_compl]


theorem rc79_tgtOrbit_top_card (A B : Finset (ConfigSpace (Fin 2))) :
    (rc78_tgtOrbit A B rc79_topTypeF).card = (rc79_reflInterF A B).card := by
  apply Finset.card_bij (fun p _ => p.1)
  · 
    intro p hp
    rw [rc78_tgtOrbit, Finset.mem_filter, rc75_prodF, Finset.mem_product] at hp
    rw [rc79_reflInterF, Finset.mem_filter]
    refine ⟨hp.1.1, ?_⟩
    have hp2 := (rc79_colTypeF_top_iff_compl p).mp hp.2
    rw [← hp2]; exact hp.1.2
  · intro p hp q hq h
    rw [rc78_tgtOrbit, Finset.mem_filter] at hp hq
    have hp2 := (rc79_colTypeF_top_iff_compl p).mp hp.2
    have hq2 := (rc79_colTypeF_top_iff_compl q).mp hq.2
    apply Prod.ext h
    rw [hp2, hq2, h]
  · intro a ha
    rw [rc79_reflInterF, Finset.mem_filter] at ha
    refine ⟨(a, rc79_complF a), ?_, rfl⟩
    rw [rc78_tgtOrbit, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [rc75_prodF, Finset.mem_product]; exact ⟨ha.1, ha.2⟩
    · rw [rc79_colTypeF_top_iff_compl]


theorem rc79_top_orbit_is_wall (A B : Finset (ConfigSpace (Fin 2))) :
    ((rc78_srcOrbit A B rc79_topTypeF).card ≤ (rc78_tgtOrbit A B rc79_topTypeF).card)
      ↔ ((rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) := by
  rw [rc79_srcOrbit_top_card, rc79_tgtOrbit_top_card]


set_option maxRecDepth 8000 in


theorem rc79_top_wall_rc72_witness :
    (rc75_disjOccF rc75_wA rc75_wB).card = 2 ∧ (rc79_reflInterF rc75_wA rc75_wB).card = 2 := by
  refine ⟨?_, ?_⟩ <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in 


theorem rc79_top_wall_fin2 :
    ∀ A B : Finset (ConfigSpace (Fin 2)),
      (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card := by
  decide


theorem rc79_perOrbitDom_fin2 : ∀ A B : Finset (ConfigSpace (Fin 2)), rc78_PerOrbitDom A B :=
  rc78_perOrbitDom_fin2


end StatMech.Walls
