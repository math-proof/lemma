/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWStrictAxisSourcePartition
import Def.StatisticalMechanics.Code.Universality.RSWInsetSourceAttachment.Part3
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_insetRightAttachmentEdge_not_mem_pathEdges {n : Int}
    (gamma delta : RlcInsetRightSourcePath n) :
    rlc_insetRightAttachmentEdge gamma ∉ rlc_pathEdges delta.1 := by
  intro he
  have hends := rlc_pathEdge_endpoints_mem_vertices delta.1 he
  have hrect := rlc_pathVertex_mem_rect delta.1 hends.1
  rw [mem_rect] at hrect
  simp at hrect


theorem rlc_insetRightAttachedPath_pathEdges_subset {n : Int}
    (gamma : RlcInsetRightSourcePath n) :
    rlc_pathEdges (rlc_insetRightAttachedPath gamma).1 ⊆
      insert (rlc_insetRightAttachmentEdge gamma)
        (rlc_pathEdges gamma.1) := by
  intro e he
  simp only [rlc_pathEdges, rlc_insetRightAttachedPath,
    SimpleGraph.Walk.edges_cons, rlc_insetRightAttachmentEdge,
    Finset.mem_insert, Finset.mem_image, List.mem_toFinset] at he ⊢
  obtain ⟨a, ha, rfl⟩ := he
  rw [List.mem_cons] at ha
  rcases ha with rfl | ha
  · left
    rfl
  · right
    simp only [SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_map, List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    refine ⟨b, hb, ?_⟩
    induction b using Sym2.inductionOn with
    | _ u v => rfl


theorem rlc_insetRightAttachedPath_open {n : Int}
    (gamma : RlcInsetRightSourcePath n)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hgamma : omega ∈ rlc_pathOpen gamma.1)
    (hattach : omega (rlc_insetRightAttachmentEdge gamma) = true) :
    omega ∈ rlc_pathOpen (rlc_insetRightAttachedPath gamma).1 := by
  intro e he
  rcases Finset.mem_insert.mp
      (rlc_insetRightAttachedPath_pathEdges_subset gamma he) with he | he
  · simpa [he] using hattach
  · exact hgamma e he


theorem rlc_insetRightAttachedPath_axis_strict {n : Int}
    (gamma : RlcInsetRightSourcePath n) :
    ∀ {z : Site 2},
      z ∈ rlc_pathVertices (rlc_insetRightAttachedPath gamma).1 ->
      z 0 = 0 -> z 1 < 0 := by
  intro z hz hz0
  simp only [rlc_pathVertices, rlc_insetRightAttachedPath,
    Finset.mem_image, List.mem_toFinset,
    SimpleGraph.Walk.support_cons, List.mem_cons] at hz
  obtain ⟨u, hu | hu, huz⟩ := hz
  · subst hu
    simpa [rlc_strictLowerHalf, ← huz] using gamma.2.1
  · simp only [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map, List.mem_map] at hu
    obtain ⟨v, _hv, hvu⟩ := hu
    have hv0 : 1 ≤ (v : Site 2) 0 := by
      have hmem := v.2
      rw [mem_rect] at hmem
      omega
    have hzu := congrArg
      (fun q : rect 0 (2 * n) (-n) n => (q : Site 2) 0) hvu
    have hu0 : (u : Site 2) 0 = 0 := by
      rw [huz]
      exact hz0
    change (v : Site 2) 0 = (u : Site 2) 0 at hzu
    omega


theorem rlc_insetRightSourceCore_to_strictAxis_mass
    (p : NNReal) (hp : p ≤ 1) (n : Int) :
    (p : Real) *
        (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
          (rlc_insetRightSourceCoreEvent n) ≤
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
        (rlc_strictAxisRightSourceEvent n) := by
  let I := RlcInsetRightSourcePath n
  let N := Fintype.card I
  let path : Fin N → I := (Fintype.equivFin I).symm
  let W : Fin N → Set (ConfigSpace (Sym2 (Site 2))) :=
    fun i => rlc_pathOpen (path i).1
  let X : Fin N → Set (ConfigSpace (Sym2 (Site 2))) :=
    fun i => {omega | omega (rlc_insetRightAttachmentEdge (path i)) = true}
  let T : Fin N → Finset (Sym2 (Site 2)) :=
    fun i => rlc_pathEdges (path i).1
  let U : Fin N → Finset (Sym2 (Site 2)) :=
    fun i => {rlc_insetRightAttachmentEdge (path i)}
  have hcover : (⋃ i, W i) = rlc_insetRightSourceCoreEvent n := by
    rw [rlc_insetRightSourceCoreEvent,
      ← rlc_iUnion_restrictedPathOpen]
    ext omega
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨path i, ?_⟩
      simpa [W] using hi
    · rintro ⟨gamma, hgamma⟩
      refine ⟨Fintype.equivFin I gamma, ?_⟩
      simpa [W, path] using hgamma
  rw [← hcover]
  apply rlc_exploration_lower_bound p hp W X T U
    (rlc_strictAxisRightSourceEvent n) (p : Real)
  · exact_mod_cast p.2
  · intro i
    exact rlc_pathOpen_dependsOn (path i).1
  · intro i
    simpa [X, U] using
      coord_true_dependsOn (rlc_insetRightAttachmentEdge (path i))
  · intro i
    rw [Finset.disjoint_left]
    intro e heT heU
    have heEq : e = rlc_insetRightAttachmentEdge (path i) := by
      simpa [U] using heU
    subst e
    simp only [rlc_exploredSupport, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_univ, true_and] at heT
    obtain ⟨j, _hji, hePath⟩ := heT
    exact rlc_insetRightAttachmentEdge_not_mem_pathEdges
      (path i) (path j) hePath
  · intro i
    simpa [X] using
      (coord_true_prob (E := Sym2 (Site 2)) p hp
        (rlc_insetRightAttachmentEdge (path i))).ge
  · intro i omega homega
    have hpath : omega ∈ rlc_pathOpen (path i).1 :=
      (rlc_mem_firstWitness_iff.mp homega.1).1
    have hopen := rlc_insetRightAttachedPath_open
      (path i) hpath homega.2
    apply Set.mem_iUnion.mpr
    exact ⟨⟨rlc_insetRightAttachedPath (path i),
      rlc_insetRightAttachedPath_axis_strict (path i)⟩, hopen⟩

end
end StatMech.Universality
