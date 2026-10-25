/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetLeftSourceAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetSourceAttachment.Part2
import Def.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part3
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_insetLeftAttachmentEdge_not_mem_pathEdges {n : Int} (gamma delta : RlcInsetLeftSourcePath n) :
    rlc_insetLeftAttachmentEdge gamma ∉ rlc_pathEdges delta.1 := by
  intro he
  have hends:=rlc_pathEdge_endpoints_mem_vertices delta.1 he
  have hrect:=rlc_pathVertex_mem_rect delta.1 hends.2
  rw [mem_rect] at hrect
  simp at hrect

theorem rlc_insetLeftAttachedPath_pathEdges_subset {n : Int} (gamma : RlcInsetLeftSourcePath n) :
    rlc_pathEdges (rlc_insetLeftAttachedPath gamma).1 ⊆
      insert (rlc_insetLeftAttachmentEdge gamma) (rlc_pathEdges gamma.1) := by
  intro e he
  simp only [rlc_pathEdges,rlc_insetLeftAttachedPath,SimpleGraph.Walk.edges_concat,
    rlc_insetLeftAttachmentEdge,Finset.mem_insert,Finset.mem_image,List.mem_toFinset] at he ⊢
  obtain ⟨a,ha,rfl⟩:=he
  simp only [List.concat_eq_append,List.mem_append,List.mem_singleton] at ha
  rcases ha with ha | rfl
  · right
    simp only [SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_map,List.mem_map] at ha
    obtain ⟨b,hb,rfl⟩:=ha
    refine ⟨b,hb,?_⟩
    induction b using Sym2.inductionOn with
    | _ u v => rfl
  · left
    rfl

theorem rlc_insetLeftAttachedPath_open {n : Int} (gamma : RlcInsetLeftSourcePath n)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hg : omega ∈ rlc_pathOpen gamma.1) (he : omega (rlc_insetLeftAttachmentEdge gamma) = true) :
    omega ∈ rlc_pathOpen (rlc_insetLeftAttachedPath gamma).1 := by
  intro e h
  rcases Finset.mem_insert.mp (rlc_insetLeftAttachedPath_pathEdges_subset gamma h) with h | h
  · simpa [h] using he
  · exact hg e h

theorem rlc_insetLeftAttachedPath_axis_strict {n : Int} (gamma : RlcInsetLeftSourcePath n) :
    ∀ {z:Site 2}, z ∈ rlc_pathVertices (rlc_insetLeftAttachedPath gamma).1 ->
      z 0=0 -> 0<z 1 := by
  intro z hz hz0
  simp only [rlc_pathVertices,rlc_insetLeftAttachedPath,Finset.mem_image,List.mem_toFinset,
    SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at hz
  obtain ⟨u,hu,huz⟩:=hz
  rcases hu with hu | hu
  · simp only [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map,List.mem_map] at hu
    obtain ⟨v,_hv,hvu⟩:=hu
    have hv0 : (v:Site 2) 0 ≤ -1 := by
      have hmem:=v.2
      rw [mem_rect] at hmem
      omega
    have hzu:=congrArg (fun q : rect (-2 * n) 0 (-n) n => (q:Site 2) 0) hvu
    have hu0 : (u:Site 2) 0=0 := by rw [huz]; exact hz0
    change (v:Site 2) 0=(u:Site 2) 0 at hzu
    omega
  · subst hu
    simpa [rlc_strictUpperHalf,← huz] using gamma.2.2

end
end StatMech.Universality
