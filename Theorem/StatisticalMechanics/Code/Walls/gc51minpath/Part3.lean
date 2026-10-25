/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc50threereplica.Part3
import Def.StatisticalMechanics.Code.Walls.gc51minpath.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  switching_card₂ connK_symm exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc51_perK_dom_of_switchInjective (ends : ι → Sym2 W)
    (K : Finset ι) {o x y g : W}
    (h : gc51_SwitchInjective ends K o x y g) :
    gc50_Lblock ends K o x g ≤ gc50_Rblock ends K o x y g := by
  obtain ⟨P, hP, hinj⟩ := h
  rw [← gc51_LblockSet_card, ← gc51_RblockSet_card]
  apply Finset.card_le_card_of_injOn (fun L => L ∆ P L)
  · 
    intro L hL
    rw [Finset.mem_coe] at hL
    obtain ⟨_, _, hQ⟩ := hP L hL
    rw [Finset.mem_coe]
    exact hQ
  · 
    exact hinj


theorem gc51_disjoint_mapsInto (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hyg : y ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    {L P : Finset ι} (hL : L ∈ gc51_LblockSet ends K o x g)
    (hPVL : P ⊆ (univ \ K) \ L) (hPsrc : sources ends P = ({y, g} : Finset W)) :
    (L ∆ P) ∈ gc51_RblockSet ends K o x y g := by
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
  obtain ⟨hLV, hLsrc, hgate⟩ := hL
  obtain ⟨hQV, hQsrc, hoxQ, hoyQ, hogQ⟩ :=
    gc51_mapsInto ends hnd K hox hyg hKsrc hLV hPVL hLsrc hPsrc hgate
  have hdisj : Disjoint L P := gc51_remPath_disjoint hPVL
  have hun : L ∆ P = L ∪ P := Disjoint.symmDiff_eq_sup hdisj
  rw [gc51_RblockSet, Finset.mem_filter, Finset.mem_powerset, hun]
  exact ⟨hQV, hQsrc, hoxQ, hoyQ, hogQ⟩


theorem gc51_complSources (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W)) :
    sources ends (univ \ K) = ({y, g} : Finset W) := by
  rw [gc40_sources_compl, huniv, hKsrc]
  exact gc50_sd_oxyg_ox hoy hog hxy hxg


theorem gc51_perKDom_of_switchInjective (ends : ι → Sym2 W)
    {o x y g : W}
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc51_SwitchInjective ends K o x y g) :
    gc50_PerKDom ends o x y g := by
  intro K hK
  exact gc51_perK_dom_of_switchInjective ends K (h K hK)


theorem gc51_countIneq_of_switchInjective (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc51_SwitchInjective ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc50_countIneq_of_perKDom ends hnd hox hoy hog hxy hxg hyg huniv
    (gc51_perKDom_of_switchInjective ends h)

end Abstract

open Classical


theorem gc51_witness_LblockSet_K13 :
    gc51_LblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 3 = {(∅ : Finset (Fin 4))} := by
  rw [gc51_LblockSet]
  have hV : (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) := by
    decide
  rw [hV]
  have hset : ({0, 2} : Finset (Fin 4)).powerset.filter
      (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))
      = {(∅ : Finset (Fin 4))} := by decide
  rw [show ({0, 2} : Finset (Fin 4)).powerset.filter
        (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ L) 1 3)
      = (({0, 2} : Finset (Fin 4)).powerset.filter
          (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))).filter
            (fun L => connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hconn : connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ (∅ : Finset (Fin 4))) 1 3 := by
    rw [Finset.union_empty]
    exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_singleton, if_pos hconn]


theorem gc51_witness_LblockSet_K23 :
    gc51_LblockSet gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 3 = {(∅ : Finset (Fin 4))} := by
  rw [gc51_LblockSet]
  have hV : (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) := by
    decide
  rw [hV]
  have hset : ({0, 1} : Finset (Fin 4)).powerset.filter
      (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))
      = {(∅ : Finset (Fin 4))} := by decide
  rw [show ({0, 1} : Finset (Fin 4)).powerset.filter
        (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ L) 1 3)
      = (({0, 1} : Finset (Fin 4)).powerset.filter
          (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))).filter
            (fun L => connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hconn : connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ (∅ : Finset (Fin 4))) 1 3 := by
    rw [Finset.union_empty]
    exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_singleton, if_pos hconn]


theorem gc51_witness_RblockSet_K13 :
    gc51_RblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3
      = {({0, 2} : Finset (Fin 4))} := by
  rw [gc51_RblockSet]
  have hV : (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) := by
    decide
  rw [hV]
  have hset : ({0, 2} : Finset (Fin 4)).powerset.filter
      (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))
      = {({0, 2} : Finset (Fin 4))} := by decide
  rw [show ({0, 2} : Finset (Fin 4)).powerset.filter
        (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 1
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 2
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 3)
      = (({0, 2} : Finset (Fin 4)).powerset.filter
          (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))).filter
            (fun Q => connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 1
              ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 2
              ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hunivEq : ({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4)) = (univ : Finset (Fin 4)) := by
    decide
  have hconn : connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4))) 0 1
      ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4))) 0 2
      ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4))) 0 3 := by
    rw [hunivEq]; exact gc50_witness_univ_allConn
  rw [Finset.filter_singleton, if_pos hconn]


theorem gc51_witness_RblockSet_K23 :
    gc51_RblockSet gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3
      = {({0, 1} : Finset (Fin 4))} := by
  rw [gc51_RblockSet]
  have hV : (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) := by
    decide
  rw [hV]
  have hset : ({0, 1} : Finset (Fin 4)).powerset.filter
      (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))
      = {({0, 1} : Finset (Fin 4))} := by decide
  rw [show ({0, 1} : Finset (Fin 4)).powerset.filter
        (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 1
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 2
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 3)
      = (({0, 1} : Finset (Fin 4)).powerset.filter
          (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))).filter
            (fun Q => connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 1
              ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 2
              ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hunivEq : ({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4)) = (univ : Finset (Fin 4)) := by
    decide
  have hconn : connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4))) 0 1
      ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4))) 0 2
      ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4))) 0 3 := by
    rw [hunivEq]; exact gc50_witness_univ_allConn
  rw [Finset.filter_singleton, if_pos hconn]


theorem gc51_witness_switchInjective_K13 :
    gc51_SwitchInjective gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
  refine ⟨fun _ => (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)), ?_, ?_⟩
  · intro L hL
    rw [gc51_witness_LblockSet_K13, Finset.mem_singleton] at hL
    subst hL
    refine ⟨Finset.Subset.refl _, ?_, ?_⟩
    · decide
    · rw [gc51_witness_RblockSet_K13, Finset.mem_singleton]; decide
  · rw [gc51_witness_LblockSet_K13]
    intro a ha b hb _
    rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
    rw [ha, hb]


theorem gc51_witness_switchInjective_K23 :
    gc51_SwitchInjective gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
  refine ⟨fun _ => (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)), ?_, ?_⟩
  · intro L hL
    rw [gc51_witness_LblockSet_K23, Finset.mem_singleton] at hL
    subst hL
    refine ⟨Finset.Subset.refl _, ?_, ?_⟩
    · decide
    · rw [gc51_witness_RblockSet_K23, Finset.mem_singleton]; decide
  · rw [gc51_witness_LblockSet_K23]
    intro a ha b hb _
    rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
    rw [ha, hb]


theorem gc51_witness_perKDom_via_switchInjective :
    gc50_PerKDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  apply gc51_perKDom_of_switchInjective gc49_witnessEnds
  intro K hK
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with rfl | rfl
  · exact gc51_witness_switchInjective_K13
  · exact gc51_witness_switchInjective_K23


theorem gc51_witness_EMassResidue_via_switchInjective :
    gc42_EMassResidue gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  gc50_EMassResidue_of_perKDom gc49_witnessEnds gc49_witnessEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide)
    gc51_witness_perKDom_via_switchInjective


end StatMech.Walls
