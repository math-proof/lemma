/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenPeel.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace2.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jvp_not_isAcyclic_of_even_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v)) (hne : G.edgeSet.Nonempty) : ¬ G.IsAcyclic := by
  classical
  intro hacyc
  obtain ⟨e, he⟩ := hne
  obtain ⟨a, b⟩ := e
  have hadj : G.Adj a b := by rwa [SimpleGraph.mem_edgeSet] at he
  set C := G.connectedComponentMk a with hC
  set s : Set V := (C.supp : Set V) with hs
  haveI : Fintype ↥s := Fintype.ofFinite _
  haveI : DecidableRel (G.induce s).Adj := Classical.decRel _
  
  have has : a ∈ s := by rw [hs, SimpleGraph.ConnectedComponent.mem_supp_iff, hC]
  have hbs : b ∈ s := by
    rw [hs, SimpleGraph.ConnectedComponent.mem_supp_iff, hC, SimpleGraph.ConnectedComponent.eq]
    exact hadj.symm.reachable
  
  have hGs_conn : (G.induce s).Connected := C.connected_toSimpleGraph
  have hGs_acyc : (G.induce s).IsAcyclic := hacyc.induce _
  have hGs_tree : (G.induce s).IsTree := ⟨hGs_conn, hGs_acyc⟩
  
  haveI : Nontrivial ↥s :=
    ⟨⟨⟨a, has⟩, ⟨b, hbs⟩, fun h => G.ne_of_adj hadj (Subtype.ext_iff.mp h)⟩⟩
  
  obtain ⟨v, hv⟩ := hGs_tree.exists_vert_degree_one_of_nontrivial
  
  have hsub : G.neighborSet ↑v ⊆ s := jeb_neighborSet_subset_component G C v
  have hdeg : (G.induce s).degree v = G.degree ↑v := jeb_degree_induce_eq' G s v hsub
  have hone : G.degree ↑v = 1 := hdeg ▸ hv
  exact (Nat.not_odd_iff_even.mpr (heven ↑v)) (hone ▸ ⟨0, rfl⟩)


theorem jvp_exists_nonbridge_edge_of_even_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v)) (hne : G.edgeSet.Nonempty) :
    ∃ a b : V, G.Adj a b ∧ (G.deleteEdges {s(a, b)}).Reachable a b := by
  classical
  have hnacyc := jvp_not_isAcyclic_of_even_nonempty G heven hne
  rw [isAcyclic_iff_forall_edge_isBridge] at hnacyc
  push Not at hnacyc
  obtain ⟨e, he, hnb⟩ := hnacyc
  obtain ⟨a, b⟩ := e
  have hadj : G.Adj a b := by rwa [SimpleGraph.mem_edgeSet] at he
  refine ⟨a, b, hadj, ?_⟩
  by_contra hnr
  exact hnb (SimpleGraph.isBridge_iff.mpr hnr)


theorem jvp_one_le_nullity_of_even_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v)) (hne : G.edgeSet.Nonempty) : 1 ≤ nullity G := by
  classical
  obtain ⟨a, b, hadj, hr⟩ := jvp_exists_nonbridge_edge_of_even_nonempty G heven hne
  have hab : s(a, b) ∈ G.edgeSet := by rwa [SimpleGraph.mem_edgeSet]
  set G' := G.deleteEdges {s(a, b)} with hG'
  have hGeq : G = G' ⊔ edge a b := deleteEdges_sup_edge_eq G a b hab
  have hne_ab : a ≠ b := G.ne_of_adj hadj
  have hadj' : ¬ G'.Adj a b := by simp [hG', deleteEdges_adj]
  have hface : faceCount G = faceCount G' + 1 := by
    rw [hGeq]; exact faceCount_sup_edge_of_reachable G' hne_ab hadj' hr
  unfold faceCount at hface
  omega


theorem jvp_abstract_even_of_closedContour (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    [DecidableRel K.Adj] (hKle : K ≤ P.G)
    (hcc : jce_ClosedContour (jei_pushGraph P K).edgeSet) :
    ∀ v : P.V, Even (Nat.card (K.neighborSet v)) := by
  classical
  haveI : Fintype P.V := Fintype.ofFinite _
  haveI : ∀ v : P.V, Fintype (K.neighborSet v) := fun v => Fintype.ofFinite _
  haveI hlf : SimpleGraph.LocallyFinite (jei_pushGraph P K) :=
    jfc_pushGraph_locallyFinite P K hKle
  have hsub : jei_pushGraph P K ≤ hypercubicLattice 2 :=
    jfc_pushGraph_le_lattice P K hKle
  intro v
  have hncard : Nat.card (K.neighborSet v) = K.degree v :=
    (Nat.card_eq_fintype_card).trans (SimpleGraph.card_neighborSet_eq_degree K v)
  rw [hncard]
  have hcorner := hcc (P.emb v)
  rw [jeb_jce_degree_eq_degree (jei_pushGraph P K) hsub (P.emb v)] at hcorner
  have hdt : (jei_pushGraph P K).degree (P.emb v) = K.degree v :=
    jcx_pushGraph_degree_corner P K v
  rw [hdt] at hcorner
  exact hcorner


end Lattice
end StatMech
