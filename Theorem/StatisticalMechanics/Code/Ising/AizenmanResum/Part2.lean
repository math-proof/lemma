/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanInclusionExclusion.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanHdom.Part2
import Def.StatisticalMechanics.Code.Ising.AizenmanResum
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

open StatMech.Sharpness.RandomCurrent


local notation "srcK" => StatMech.Sharpness.RandomCurrent.sources

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


theorem ght_backboneAvgDom_holds_of_no_allConn (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (A : Finset V) {o x y : V} (Φ : Finset ι → Finset ι → ℝ)
    (hno : M.filter (fun m => aie_allConn ends m o x y) = ∅) :
    ght_backboneAvgDom ends M A o x y Φ := by
  unfold ght_backboneAvgDom
  rw [hno, Finset.sum_empty, Finset.sum_empty, mul_zero]


theorem ght_tri_backbones :
    ght_backbones ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 1 2
      = {{1}, {0, 2}} := by
  unfold ght_backbones
  decide


theorem ght_tri_removed_conn_1 :
    connK ahd_triEnds (({0, 1, 2} : Finset (Fin 3)) ∆ ({1} : Finset (Fin 3))) 1 2 := by
  have h : (({0, 1, 2} : Finset (Fin 3)) ∆ ({1} : Finset (Fin 3))) = {0, 2} := by decide
  rw [h]
  refine Relation.ReflTransGen.head (b := 0) ?_
    (Relation.ReflTransGen.single (a := 0) (b := 2) ?_)
  · exact ⟨0, by decide, by decide, by decide, by decide⟩
  · exact ⟨2, by decide, by decide, by decide, by decide⟩


theorem ght_tri_removed_conn_2 :
    connK ahd_triEnds (({0, 1, 2} : Finset (Fin 3)) ∆ ({0, 2} : Finset (Fin 3))) 1 2 := by
  have h : (({0, 1, 2} : Finset (Fin 3)) ∆ ({0, 2} : Finset (Fin 3))) = {1} := by decide
  rw [h]
  exact Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩


theorem ght_tri_resummed_filter_empty :
    (ght_backbones ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 1 2).filter
      (fun P => aie_noneConn ahd_triEnds (({0, 1, 2} : Finset (Fin 3)) ∆ P) 0 1 2) = ∅ := by
  rw [ght_tri_backbones, Finset.filter_eq_empty_iff]
  intro P hP
  simp only [Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with rfl | rfl
  · rintro ⟨h1, _, _⟩; exact h1 ght_tri_removed_conn_1
  · rintro ⟨h1, _, _⟩; exact h1 ght_tri_removed_conn_2


theorem ght_tri_resummedNoneMass_zero :
    ght_resummedNoneMass ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) (fun _ => 1)
        (srcK ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) 0 1 2 = 0 := by
  unfold ght_resummedNoneMass
  rw [ght_tri_resummed_filter_empty, Finset.sum_empty]


theorem ght_backboneAvgDom_refutable :
    ¬ ght_backboneAvgDom ahd_triEnds ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3)))
        (srcK ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) 0 1 2 (fun _ _ => 1) := by
  unfold ght_backboneAvgDom
  intro hdom
  set m₀ : Finset (Fin 3) := {0, 1, 2} with hm₀
  set A₀ : Finset (Fin 3) := srcK ahd_triEnds m₀ with hA₀
  have hall : aie_allConn ahd_triEnds m₀ 0 1 2 := ahd_tri_allConn
  
  rw [Finset.filter_singleton, if_pos hall, Finset.sum_singleton, Finset.sum_singleton] at hdom
  
  rw [ght_tri_resummedNoneMass_zero] at hdom
  have hpos : (0 : ℝ) < aie_mass ahd_triEnds m₀ (fun _ => 1) A₀ := ahd_tri_mass_pos
  linarith

end Ising
end StatMech
