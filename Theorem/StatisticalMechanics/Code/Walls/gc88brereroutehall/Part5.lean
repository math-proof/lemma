/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean -/

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
import Def.StatisticalMechanics.Code.Walls.gc88brereroutehall.Part5
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


theorem gc88b_wred_sources :
    sources gc88b_wredEnds (univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
  decide


theorem gc88b_connK_color_invariant (ends : ι → Sym2 W) (K : Finset ι) (c : W → Bool)
    (hc : ∀ i ∈ K, ∀ a b : W, a ∈ ends i → b ∈ ends i → c a = c b) {a b : W}
    (h : connK ends K a b) : c a = c b := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      obtain ⟨i, hi, hpa, hpb, _⟩ := hstep
      rw [ih]; exact hc i hi _ _ hpa hpb


theorem gc88b_wred_cogxg_fibers_card :
    (((univ : Finset (Fin 4)).powerset.filter
        (fun K => sources gc88b_wredEnds K = ({0, 3} : Finset (Fin 4)))).filter
      (fun K₁ => connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ K₁) 1 3))
      = ({{1}, {2}} : Finset (Finset (Fin 4))) := by
  
  
  have hbase : ((univ : Finset (Fin 4)).powerset.filter
      (fun K => sources gc88b_wredEnds K = ({0, 3} : Finset (Fin 4))))
      = ({{1}, {2}} : Finset (Finset (Fin 4))) := by decide
  rw [hbase]
  rw [Finset.filter_true_of_mem]
  intro K hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  
  rcases hK with rfl | rfl
  · 
    refine Relation.ReflTransGen.head (b := (0 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩)
  · 
    refine Relation.ReflTransGen.head (b := (0 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩)


theorem gc88b_wred_T3_fibers_card :
    (((univ : Finset (Fin 4)).powerset.filter
        (fun K => sources gc88b_wredEnds K = (∅ : Finset (Fin 4)))).filter
      (fun J₁ => connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 1
        ∧ connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 2
        ∧ connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 3))
      = ({∅} : Finset (Finset (Fin 4))) := by
  have hbase : ((univ : Finset (Fin 4)).powerset.filter
      (fun K => sources gc88b_wredEnds K = (∅ : Finset (Fin 4))))
      = ({∅, {1, 2}} : Finset (Finset (Fin 4))) := by decide
  rw [hbase]
  ext J
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hJ | hJ, hconn⟩
    · exact hJ
    · 
      exfalso
      subst hJ
      
      have := gc88b_connK_color_invariant gc88b_wredEnds ((univ : Finset (Fin 4)) \ {1, 2})
        (fun v => decide (v = 0 ∨ v = 1)) (by decide) hconn.2.2
      simp at this
  · rintro rfl
    refine ⟨Or.inl rfl, ?_, ?_, ?_⟩
    
    · exact Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩
    · refine Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨1, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩


theorem gc88b_wred_fiber_injection_impossible :
    
    #(gc88b_cogxgSet gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3) = 2
      ∧ #(gc88b_T3Set gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3)
          = gc87b_T3 gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3
    
      ∧ #(((univ : Finset (Fin 4)).powerset.filter
            (fun K => sources gc88b_wredEnds K = ({0, 3} : Finset (Fin 4)))).filter
          (fun K₁ => connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ K₁) 1 3))
        > #(((univ : Finset (Fin 4)).powerset.filter
            (fun K => sources gc88b_wredEnds K = (∅ : Finset (Fin 4)))).filter
          (fun J₁ => connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 1
            ∧ connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 2
            ∧ connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 3)) := by
  refine ⟨?_, gc88b_T3Set_card _ _ _ _ _ _, ?_⟩
  · unfold gc88b_cogxgSet; decide
  · rw [gc88b_wred_cogxg_fibers_card, gc88b_wred_T3_fibers_card]
    decide


theorem gc88b_tri_marriage :
    gc88b_Marriage gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3 :=
  (gc88b_marriage_iff_cogxg_le_T3 gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3).2
    (gc87b_tri_residue_nonvacuous.2)


theorem gc88b_hall_status (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    
    (∀ KK JJ, KK ∈ gc88b_cogxgSet ends m o x y g → JJ ∈ gc88b_T3Set ends m o x y g →
        gc88b_reroute ends o g KK JJ)
    
    ∧ (gc88b_Marriage ends m o x y g ↔ gc87b_CogxgLeT3 ends m o x y g)
    
    ∧ (gc88b_Marriage ends m o x y g → gc85b_ThreeCurrentBijection ends m o x y g) :=
  ⟨fun KK JJ hKK hJJ => gc88b_reroute_total ends m o x y g hKK hJJ,
   gc88b_marriage_iff_cogxg_le_T3 ends m o x y g,
   fun hM => gc88b_close_of_marriage ends m hnd hsrc hox hoy hog hM⟩


theorem gc88b_machine_findings : True := trivial

end StatMech.Walls
