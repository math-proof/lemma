/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc89bmetricinjection.lean -/

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
import Def.StatisticalMechanics.Code.Walls.gc89bmetricinjection
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


theorem gc89b_ntEnds_sources :
    sources gc89b_ntEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
  decide


theorem gc89b_metric_nontotal :
    
    sources gc89b_ntEnds (({0} : Finset (Fin 5)) ∆ ({1, 3} : Finset (Fin 5)))
        = ({0, 3} : Finset (Fin 4))
    
      ∧ ¬ gc89b_metricReroute gc89b_ntEnds 0 1 3
          (({0} : Finset (Fin 5)), ({2} : Finset (Fin 5)))
          (({1, 3} : Finset (Fin 5)), (∅ : Finset (Fin 5))) := by
  refine ⟨by decide, ?_⟩
  intro h
  obtain ⟨⟨_, hdeg⟩, _⟩ := h
  have := hdeg 3
  revert this; decide


theorem gc89b_canonical_collision :
    
    
    (({1} : Finset (Fin 4)) \ ({1} : Finset (Fin 4)) = (∅ : Finset (Fin 4)))
      ∧ (({2} : Finset (Fin 4)) \ ({2} : Finset (Fin 4)) = (∅ : Finset (Fin 4)))
      ∧ sources gc88b_wredEnds ({1} : Finset (Fin 4)) = ({0, 3} : Finset (Fin 4))
      ∧ sources gc88b_wredEnds ({2} : Finset (Fin 4)) = ({0, 3} : Finset (Fin 4)) := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> decide


theorem gc89b_tri_reroute_lands :
    sources gc87b_triEnds (({0} : Finset (Fin 3))) = ({0, 3} : Finset (Fin 4))
      ∧ ({0} : Finset (Fin 3)) \ ({0} : Finset (Fin 3)) = (∅ : Finset (Fin 3))
      ∧ connK gc87b_triEnds ((univ : Finset (Fin 3)) \ (∅ : Finset (Fin 3))) 0 1
      ∧ connK gc87b_triEnds ((univ : Finset (Fin 3)) \ (∅ : Finset (Fin 3))) 0 2
      ∧ connK gc87b_triEnds ((univ : Finset (Fin 3)) \ (∅ : Finset (Fin 3))) 0 3 := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · rw [Finset.sdiff_empty]
    refine Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩)
  · rw [Finset.sdiff_empty]
    refine Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩)
  · rw [Finset.sdiff_empty]
    exact Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩


theorem gc89b_metric_status (ends : ι → Sym2 W) {m K₁ P : Finset ι} (hK₁m : K₁ ⊆ m)
    (hP : P ⊆ K₁) (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxne : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (hK₁ : sources ends K₁ = ({o, g} : Finset W)) (hPsrc : sources ends P = ({o, g} : Finset W))
    (hxg : connK ends (m \ K₁) x g) :
    
    (sources ends (K₁ \ P) = (∅ : Finset W)
        ∧ connK ends (m \ (K₁ \ P)) o x ∧ connK ends (m \ (K₁ \ P)) o y
        ∧ connK ends (m \ (K₁ \ P)) o g)
    
    ∧ (∃ Q ⊆ K₁, sources ends Q = ({o, g} : Finset W)) := by
  refine ⟨⟨gc89b_reroute_boundary_empty ends hP hK₁ hPsrc, ?_⟩,
    gc89b_exists_ogPath ends hK₁m hnd hog hK₁⟩
  exact gc89b_reroute_lands_allConn ends hK₁m hP hnd hsrc hox hoy hog hxne hxg' hyg hK₁ hPsrc hxg


theorem gc89b_machine_findings : True := trivial

end StatMech.Walls
