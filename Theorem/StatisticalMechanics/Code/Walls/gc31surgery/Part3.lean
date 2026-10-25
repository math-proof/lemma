/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc30reroute
import Theorem.StatisticalMechanics.Code.Ising.BackboneResummation.Part2
import Theorem.StatisticalMechanics.Code.Ising.BackboneExists
import Theorem.StatisticalMechanics.Code.Ising.HdomMultiplicity.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
import Def.StatisticalMechanics.Code.Walls.gc31surgery.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc31_zero_noneConn : hnw_noneConn hmu_TriG gc31_zeroM 0 1 2 := by
  have hpos : posEdges hmu_TriG.edgeFinset gc31_zeroM = ∅ := by
    unfold posEdges gc31_zeroM
    apply Finset.filter_false_of_mem
    intro e _; simp
  rw [hnw_noneConn, hpos]
  refine ⟨?_, ?_, ?_⟩ <;> · intro h; have := gc31_connP_empty_eq h; simp at this


theorem gc31_allFilter_witness :
    bbr_allFilter hmu_TriG ({hmu_triM, gc31_zeroM} : Finset (Sharpness.Current (Fin 3))) 0 1 2
      = {hmu_triM} := by
  unfold bbr_allFilter
  ext m
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hmem, hall⟩
    rcases hmem with rfl | rfl
    · rfl
    · exact absurd hall (hnw_noneConn_not_allConn hmu_TriG gc31_zeroM gc31_zero_noneConn)
  · rintro rfl
    exact ⟨Or.inl rfl, hmu_tri_allConn⟩


theorem gc31_zero_in_noneFilter :
    gc31_zeroM ∈ bbr_noneFilter hmu_TriG
      ({hmu_triM, gc31_zeroM} : Finset (Sharpness.Current (Fin 3))) 0 1 2 := by
  unfold bbr_noneFilter
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), gc31_zero_noneConn⟩


theorem gc31_massDoubling_witness :
    gc31_MassDoublingSurgery hmu_TriG 1 (fun _ => 1)
      ({hmu_triM, gc31_zeroM} : Finset (Sharpness.Current (Fin 3))) ({0} : Finset (Fin 3)) 0 1 2 := by
  have hodd : ¬ Even ({0} : Finset (Fin 3)).card := by decide
  refine gc31_massDoubling_of_singleton_dominated hmu_TriG 1 (fun _ => 1) _ _ 0 1 2
    hmu_triM gc31_zeroM gc31_allFilter_witness gc31_zero_in_noneFilter ?_
  rw [gc31_mass_zero_of_odd_card hmu_TriG 1 (fun _ => 1) hmu_triM _ hodd,
      gc31_mass_zero_of_odd_card hmu_TriG 1 (fun _ => 1) gc31_zeroM _ hodd]
  norm_num


theorem gc31_backboneSurgery_witness :
    bbr_BackboneSurgery hmu_TriG 1 (fun _ => 1)
      ({hmu_triM, gc31_zeroM} : Finset (Sharpness.Current (Fin 3))) ({0} : Finset (Fin 3)) 0 1 2 :=
  gc31_backboneSurgery_of_massDoubling hmu_TriG 1 (fun _ => 1) _ _ 0 1 2 gc31_massDoubling_witness


theorem gc31_massDoubling_fails_triangle_emptyB :
    ¬ gc31_MassDoublingSurgery hmu_TriG 1 (fun _ => 1)
        ({hmu_triM} : Finset (Sharpness.Current (Fin 3))) (∅ : Finset (Fin 3)) 0 1 2 := by
  intro h
  exact hmu_hdom_refutable
    (bbr_hdom_of_surgery hmu_TriG 1 (fun _ => 1) (by norm_num) (fun _ => by norm_num) _ ∅ 0 1 2
      (gc31_backboneSurgery_of_massDoubling hmu_TriG 1 (fun _ => 1) _ ∅ 0 1 2 h))

end StatMech.Walls
