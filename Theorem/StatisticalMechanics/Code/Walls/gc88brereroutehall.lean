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
import Def.StatisticalMechanics.Code.Walls.gc88brereroutehall
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


theorem gc88b_cogxgSet_card (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    #(gc88b_cogxgSet ends m o x y g) = gc85b_pcount ends m {o, g} {x, g} := rfl


theorem gc88b_T3Set_card (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    #(gc88b_T3Set ends m o x y g) = gc87b_T3 ends m o x y g := by
  unfold gc88b_T3Set gc87b_T3
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun JJ => JJ.1)
        (t := (m.powerset.filter (fun K => sources ends K = ∅)).filter
          (fun J₁ => connK ends (m \ J₁) o x ∧ connK ends (m \ J₁) o y ∧ connK ends (m \ J₁) o g))
        (fun JJ hJJ => by
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_powerset] at hJJ ⊢
          exact ⟨⟨hJJ.1.1, hJJ.2.2.1⟩, hJJ.2.2.2.2⟩)]
  refine Finset.sum_congr rfl (fun J₁ hJ₁ => ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset] at hJ₁
  obtain ⟨⟨hJ₁m, hJ₁src⟩, hconn⟩ := hJ₁
  
  unfold gc86b_ncount
  symm
  apply Finset.card_bij (fun J₂ _ => (J₁, J₂))
  · intro J₂ hJ₂
    simp only [Finset.mem_filter, Finset.mem_powerset] at hJ₂
    obtain ⟨hJ₂sub, hJ₂src⟩ := hJ₂
    have hJ₂m : J₂ ⊆ m := hJ₂sub.trans Finset.sdiff_subset
    have hdis : Disjoint J₁ J₂ := by
      rw [Finset.disjoint_left]
      intro a haJ₁ haJ₂
      exact (Finset.mem_sdiff.1 (hJ₂sub haJ₂)).2 haJ₁
    rw [Finset.mem_filter]
    refine ⟨?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
    exact ⟨⟨hJ₁m, hJ₂m⟩, hdis, hJ₁src, hJ₂src, hconn.1, hconn.2.1, hconn.2.2⟩
  · intro J₂ hJ₂ J₂' hJ₂' h
    simp only [Prod.mk.injEq] at h
    exact h.2
  · rintro ⟨L₁, L₂⟩ hLL
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hLL
    obtain ⟨⟨⟨hL₁m, hL₂m⟩, hdis, hL₁src, hL₂src, _⟩, hproj⟩ := hLL
    
    subst hproj
    refine ⟨L₂, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, hL₂src⟩
    intro a ha
    rw [Finset.mem_sdiff]
    exact ⟨hL₂m ha, fun hL₁ => (Finset.disjoint_left.1 hdis) hL₁ ha⟩


end StatMech.Walls
