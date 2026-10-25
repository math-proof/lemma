/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc18mengerhard.Part3
import Def.StatisticalMechanics.Code.Walls.bc19menger.Part2


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}


theorem bc19_Bhalf_support [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) (i : Fin k) :
    ((FB.q (bc19_match hS FA FB i)).reverse.copy (bc19_match_spec hS FA FB i) rfl).support
      = (FB.q (bc19_match hS FA FB i)).support.reverse := by
  rw [Walk.support_copy, Walk.support_reverse]

theorem bc19_gluedPath_support_mem [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) (i : Fin k) {z : V} :
    z ∈ (bc19_gluedPath hS FA FB i).support ↔
      z ∈ (FA.q i).support ∨ z ∈ (FB.q (bc19_match hS FA FB i)).support := by
  rw [bc19_gluedPath, Walk.mem_support_append_iff, bc19_Bhalf_support, List.mem_reverse]

theorem bc19_gluedPath_isPath [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (hRR : RA ∩ RB ⊆ S)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) (i : Fin k) :
    (bc19_gluedPath hS FA FB i).IsPath := by
  rw [bc19_gluedPath]
  apply bc18_appendPath_of_inter (FA.hq i)
  · rw [Walk.isPath_copy]; exact (Walk.isPath_reverse_iff _).2 (FB.hq _)
  · intro z hzA hzB
    rw [bc19_Bhalf_support, List.mem_reverse] at hzB
    exact FA.hmeet i z hzA (hRR ⟨FA.hreg i z hzA, FB.hreg _ z hzB⟩)


theorem bc19_cross_eq [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (hRR : RA ∩ RB ⊆ S)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) {i j : Fin k} {z : V}
    (hzA : z ∈ (FA.q i).support) (hzB : z ∈ (FB.q (bc19_match hS FA FB j)).support) :
    FA.c i = FA.c j := by
  have hvS : z ∈ S := hRR ⟨FA.hreg i z hzA, FB.hreg _ z hzB⟩
  have h1 : z = FA.c i := FA.hmeet i z hzA hvS
  have h2 : z = FB.c (bc19_match hS FA FB j) := FB.hmeet _ z hzB hvS
  rw [bc19_match_spec hS FA FB j] at h2
  rw [← h1, ← h2]


end StatMech.Walls
