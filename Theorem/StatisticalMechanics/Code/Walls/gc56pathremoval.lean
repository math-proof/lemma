/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc55graham.Part2
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

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc56_multiRemove (ends : ι → Sym2 W) (G : Finset ι) (E : Finset ι)
    (hrec : ∀ i ∈ E, ∀ p q : W, ends i = s(p, q) → connK ends (G \ E) p q)
    {x g : W} (hx : connK ends G x g) : connK ends (G \ E) x g := by
  induction E using Finset.induction_on generalizing G with
  | empty => simpa using hx
  | @insert a E ha ih =>
    
    have hFeq : G \ (insert a E) = (G \ {a}) \ E := by
      ext j; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; tauto
    obtain ⟨⟨p, q⟩, hpq⟩ := (ends a).exists_rep
    have hpq' : ends a = s(p, q) := hpq.symm
    
    have hconn_full : connK ends (G \ (insert a E)) p q :=
      hrec a (Finset.mem_insert_self a E) p q hpq'
    
    have hsub : G \ (insert a E) ⊆ G \ {a} := by
      intro j hj; rw [Finset.mem_sdiff] at hj ⊢
      rw [Finset.mem_singleton]
      exact ⟨hj.1, fun h => hj.2 (h ▸ Finset.mem_insert_self _ _)⟩
    have hconn_a : connK ends (G \ {a}) p q := gc51_connK_mono ends hsub hconn_full
    
    have hx' : connK ends (G \ {a}) x g := by
      by_cases haG : a ∈ G
      · exact gc55_reroute ends G a haG hpq' hconn_a hx
      · rw [Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem haG]; exact hx
    
    have hrec' : ∀ i ∈ E, ∀ p' q' : W, ends i = s(p', q') → connK ends ((G \ {a}) \ E) p' q' := by
      intro i hi p' q' hpqi
      have := hrec i (Finset.mem_insert_of_mem hi) p' q' hpqi
      rwa [hFeq] at this
    have := ih (G := G \ {a}) hrec' hx'
    rwa [hFeq]


theorem gc56_graph_restrict (K L D : Finset ι) (hKD : Disjoint K D) :
    (K ∪ L) \ (L ∩ D) = K ∪ (L \ D) := by
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  rw [Finset.disjoint_left] at hKD
  constructor
  · rintro ⟨hj | hj, hnot⟩
    · exact Or.inl hj
    · exact Or.inr ⟨hj, fun hd => hnot ⟨hj, hd⟩⟩
  · rintro (hj | ⟨hjL, hjD⟩)
    · exact ⟨Or.inl hj, fun ⟨hjL, hd⟩ => hKD hj hd⟩
    · exact ⟨Or.inr hjL, fun ⟨_, hd⟩ => hjD hd⟩


end Abstract
end StatMech.Walls
