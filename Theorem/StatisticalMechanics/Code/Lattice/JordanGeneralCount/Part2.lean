/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenStep
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenPeel.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part5
import Inductive.StatisticalMechanics.Code.Lattice.JordanGeneralCount
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jgc_tc_eq_faceCount (P : PlanarZ2Subgraph) :
    ∀ {K : SimpleGraph P.V}, jgc_IsCactus K → K ≤ P.G → jic_tc P K = faceCount K := by
  classical
  haveI : Finite P.V := P.finV
  haveI : DecidableEq P.V := P.decV
  intro K hcac
  induction hcac with
  | bot =>
    intro _
    
    unfold jic_tc
    rw [jei_pushGraph_bot, jfc_whb_bot]
    have hlat : Nat.card (hypercubicLattice 2).ConnectedComponent = 1 := by
      have hreach : ∀ a b : Site 2, (hypercubicLattice 2).Reachable a b :=
        fun a b => pbs_reach_all a b
      have hsub : Subsingleton (hypercubicLattice 2).ConnectedComponent :=
        ⟨ConnectedComponent.ind₂ (fun a b => ConnectedComponent.sound (hreach a b))⟩
      haveI : Nonempty (hypercubicLattice 2).ConnectedComponent :=
        ⟨(hypercubicLattice 2).connectedComponentMk ![0, 0]⟩
      rw [Nat.card_eq_one_iff_unique]; exact ⟨hsub, inferInstance⟩
    rw [hlat]
    unfold faceCount nullity
    rw [SimpleGraph.edgeSet_bot, Set.ncard_empty, card_components_bot]; simp
  | @leaf K x z hadj huniq hrec ih =>
    intro hKle
    
    have hK'le : K.deleteEdges {s(x, z)} ≤ P.G := (deleteEdges_le _).trans hKle
    have ihK' := ih hK'le
    rw [← jgc_tc_deleteLeaf P K hKle hadj huniq, ihK', jgc_faceCount_deleteLeaf K hadj huniq]
  | @cycle K hcyc v p hp hrec ih =>
    intro hKle
    haveI hlfK : SimpleGraph.LocallyFinite K := fun w => Fintype.ofFinite _
    have hK'le : K.deleteEdges p.toSubgraph.edgeSet ≤ P.G := (deleteEdges_le _).trans hKle
    have ihK' := ih hK'le
    
    have hreg := jic_tc_deleteCycle P K hKle hcyc p hp
    have hface := jvp_faceCount_deleteCycle K hcyc p hp
    rw [hreg, ihK']; omega


theorem jgc_total_count (P : PlanarZ2Subgraph) (hcac : jgc_IsCactus P.G) :
    Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = faceCount P.G := by
  have h := jgc_tc_eq_faceCount P hcac le_rfl
  unfold jic_tc at h
  rwa [jei_pushGraph_G P] at h


theorem jgc_faithfulRegionCount_eq_nullity (P : PlanarZ2Subgraph) (hcac : jgc_IsCactus P.G) :
    whc_faithfulRegionCount P = nullity P.G := by
  have htot := jgc_total_count P hcac
  have hcard := jfc_whb_bounded_add_one_eq_card P
  rw [htot, faceCount] at hcard
  omega


theorem jgc_faithfulDiscreteJordan (P : PlanarZ2Subgraph) (hcac : jgc_IsCactus P.G) :
    whc_FaithfulDiscreteJordan P := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph P)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph P) (Set.toFinite (imageGraph P).edgeSet)
  have heq : whc_faithfulRegionCount P = nullity P.G :=
    jgc_faithfulRegionCount_eq_nullity P hcac
  unfold whc_faithfulRegionCount at heq
  exact ⟨Finite.equivFinOfCardEq heq⟩


theorem jgc_isCactus_of_isCycles {V : Type*} [Finite V] [DecidableEq V]
    (K : SimpleGraph V) (hcyc : K.IsCycles) : jgc_IsCactus K := by
  classical
  haveI : Fintype V := Fintype.ofFinite _
  generalize hn : K.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    haveI hlfK : SimpleGraph.LocallyFinite K := fun w => Fintype.ofFinite _
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · subst hz
      have hempty : K.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite K.edgeSet)).mp hn
      have hbot : K = ⊥ := by rw [← edgeSet_eq_empty]; exact hempty
      subst hbot; exact jgc_IsCactus.bot
    · have hne : K.edgeSet.Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hn]; exact hpos
      obtain ⟨e, he⟩ := hne
      obtain ⟨a, b⟩ := e
      rw [SimpleGraph.mem_edgeSet] at he
      have hnbr : (K.neighborSet a).Nonempty := ⟨b, he⟩
      obtain ⟨p, hpc, _⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
        (v := a) (c := K.connectedComponentMk a) rfl hnbr
      have hK'cyc : (K.deleteEdges p.toSubgraph.edgeSet).IsCycles :=
        jvp_isCycles_deleteCycle_isCycles hcyc p hpc
      have hlt : (K.deleteEdges p.toSubgraph.edgeSet).edgeSet.ncard < K.edgeSet.ncard :=
        jvp_ncard_deleteCycle_lt p hpc
      refine jgc_IsCactus.cycle hcyc p hpc (ih _ (by omega) _ hK'cyc rfl)


theorem jgc_isCactus_of_isAcyclic {V : Type*} [Finite V] [DecidableEq V]
    (K : SimpleGraph V) (hacyc : K.IsAcyclic) : jgc_IsCactus K := by
  classical
  haveI : Fintype V := Fintype.ofFinite _
  generalize hn : K.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    haveI hdec : DecidableRel K.Adj := Classical.decRel _
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · subst hz
      have hempty : K.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite K.edgeSet)).mp hn
      have hbot : K = ⊥ := by rw [← edgeSet_eq_empty]; exact hempty
      subst hbot; exact jgc_IsCactus.bot
    · have hne : K.edgeSet.Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hn]; exact hpos
      
      
      obtain ⟨e, he⟩ := hne
      obtain ⟨a, b⟩ := e
      rw [SimpleGraph.mem_edgeSet] at he
      
      set C := K.connectedComponentMk a with hC
      set s : Set V := (C.supp : Set V) with hs
      haveI : Fintype ↥s := Fintype.ofFinite _
      haveI : DecidableRel (K.induce s).Adj := Classical.decRel _
      have has : a ∈ s := by rw [hs, SimpleGraph.ConnectedComponent.mem_supp_iff, hC]
      have hbs : b ∈ s := by
        rw [hs, SimpleGraph.ConnectedComponent.mem_supp_iff, hC, SimpleGraph.ConnectedComponent.eq]
        exact he.symm.reachable
      have hGs_conn : (K.induce s).Connected := C.connected_toSimpleGraph
      have hGs_acyc : (K.induce s).IsAcyclic := hacyc.induce _
      have hGs_tree : (K.induce s).IsTree := ⟨hGs_conn, hGs_acyc⟩
      haveI : Nontrivial ↥s :=
        ⟨⟨⟨a, has⟩, ⟨b, hbs⟩, fun h => K.ne_of_adj he (Subtype.ext_iff.mp h)⟩⟩
      obtain ⟨u, hu⟩ := hGs_tree.exists_vert_degree_one_of_nontrivial
      
      have hsub : K.neighborSet ↑u ⊆ s := jeb_neighborSet_subset_component K C u
      have hdeg : (K.induce s).degree u = K.degree ↑u := jeb_degree_induce_eq' K s u hsub
      have hone : K.degree ↑u = 1 := hdeg ▸ hu
      
      rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_one] at hone
      obtain ⟨z, hz⟩ := hone
      have hadjuz : K.Adj ↑u z := by
        have : z ∈ K.neighborFinset ↑u := by rw [hz]; exact Finset.mem_singleton_self z
        rwa [SimpleGraph.mem_neighborFinset] at this
      have huniq : ∀ w, K.Adj ↑u w → w = z := by
        intro w hw
        have : w ∈ K.neighborFinset ↑u := by rw [SimpleGraph.mem_neighborFinset]; exact hw
        rw [hz, Finset.mem_singleton] at this; exact this
      
      have hK'acyc : (K.deleteEdges {s(↑u, z)}).IsAcyclic := hacyc.anti (deleteEdges_le _)
      have hmem : s(↑u, z) ∈ K.edgeSet := by rwa [SimpleGraph.mem_edgeSet]
      have hlt : (K.deleteEdges {s(↑u, z)}).edgeSet.ncard < K.edgeSet.ncard := by
        rw [edgeSet_deleteEdges]
        have hssub : K.edgeSet \ {s(↑u, z)} ⊂ K.edgeSet :=
          ⟨Set.diff_subset, fun hcontra => (hcontra hmem).2 rfl⟩
        exact Set.ncard_lt_ncard hssub (Set.toFinite _)
      exact jgc_IsCactus.leaf hadjuz huniq (ih _ (by omega) _ hK'acyc rfl)


end Lattice
end StatMech
