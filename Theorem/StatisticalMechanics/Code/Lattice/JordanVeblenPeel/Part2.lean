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
import Def.StatisticalMechanics.Code.Lattice.JordanVeblenPeel
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jvp_evenPeel_of_steps (P : PlanarZ2Subgraph)
    (hveb : jvp_VeblenStep P) (hreg : jvp_RegionStep P) : jcx_EvenPeel P := by
  intro K hKle hcc hKne
  obtain ⟨K', hK'leK, hcc', hlt, hface⟩ := hveb K hKle hcc hKne
  exact ⟨K', hK'leK.trans hKle, hcc', hlt, hface, hreg K K' hKle hK'leK hcc hcc' hlt hface⟩


theorem jvp_faithfulCountResidue_of_steps
    (h : ∀ (P : PlanarZ2Subgraph), jeb_EvenDegreeSubgraph P →
      jvp_VeblenStep P ∧ jvp_RegionStep P) :
    jeb_FaithfulCountResidue :=
  jcx_faithfulCountResidue_of_evenPeel
    (fun P hP => jvp_evenPeel_of_steps P (h P hP).1 (h P hP).2)


theorem jvp_veblenStep_unitSquare : jvp_VeblenStep jbc_Pce := by
  classical
  intro K hKle hcc hKne
  haveI hdec : DecidableRel K.Adj := Classical.decRel _
  have heven : ∀ i : Fin 4, Even (Nat.card (K.neighborSet i)) :=
    jvp_abstract_even_of_closedContour jbc_Pce K hKle hcc
  rcases jcx_square_even_subgraph K hKle heven with hbot | hfull
  · exact absurd hbot hKne
  · subst hfull
    obtain ⟨_, _, hlt, hface, _⟩ := jcx_square_peel_witness
    refine ⟨⊥, bot_le, ?_, hlt, hface⟩
    rw [jei_pushGraph_bot jbc_Pce, SimpleGraph.edgeSet_bot]
    have h := jce_empty_closedContour
    rwa [Finset.coe_empty] at h


theorem jvp_regionStep_unitSquare : jvp_RegionStep jbc_Pce := by
  classical
  intro K K' hKle hK'leK hcc hcc' hlt hface
  haveI hdecK : DecidableRel K.Adj := Classical.decRel _
  haveI hdecK' : DecidableRel K'.Adj := Classical.decRel _
  have hK'le : K' ≤ jbc_Pce.G := hK'leK.trans hKle
  
  have hKne : K ≠ ⊥ := by
    intro hb; rw [hb, SimpleGraph.edgeSet_bot, Set.ncard_empty] at hlt; omega
  have hevenK : ∀ i : Fin 4, Even (Nat.card (K.neighborSet i)) :=
    jvp_abstract_even_of_closedContour jbc_Pce K hKle hcc
  have hevenK' : ∀ i : Fin 4, Even (Nat.card (K'.neighborSet i)) :=
    jvp_abstract_even_of_closedContour jbc_Pce K' hK'le hcc'
  rcases jcx_square_even_subgraph K hKle hevenK with hKbot | hKfull
  · exact absurd hKbot hKne
  · 
    subst hKfull
    rcases jcx_square_even_subgraph K' hK'le hevenK' with hK'bot | hK'full
    · 
      subst hK'bot
      obtain ⟨_, _, _, _, hdual⟩ := jcx_square_peel_witness
      
      exact hdual
    · 
      exfalso; rw [hK'full] at hlt; omega


theorem jvp_faithfulDiscreteJordan_unitSquare : whc_FaithfulDiscreteJordan jbc_Pce :=
  jcx_faithfulDiscreteJordan_of_evenResidue jbc_Pce jeb_square_closedContour
    (jcx_evenCountResidue_of_evenPeel jbc_Pce
      (jvp_evenPeel_of_steps jbc_Pce jvp_veblenStep_unitSquare jvp_regionStep_unitSquare))


theorem jvp_faceCount_deleteEdges_nonbridge {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) {a b : V} (hab : G.Adj a b)
    (hr : (G.deleteEdges {s(a, b)}).Reachable a b) :
    faceCount (G.deleteEdges {s(a, b)}) + 1 = faceCount G := by
  classical
  have hmem : s(a, b) ∈ G.edgeSet := by rwa [SimpleGraph.mem_edgeSet]
  set G' := G.deleteEdges {s(a, b)} with hG'
  have hGeq : G = G' ⊔ edge a b := deleteEdges_sup_edge_eq G a b hmem
  have hne_ab : a ≠ b := G.ne_of_adj hab
  have hadj' : ¬ G'.Adj a b := by simp [hG', deleteEdges_adj]
  have hface : faceCount G = faceCount G' + 1 := by
    rw [hGeq]; exact faceCount_sup_edge_of_reachable G' hne_ab hadj' hr
  omega


theorem jvp_summary :
    (∀ (P : PlanarZ2Subgraph), jvp_VeblenStep P → jvp_RegionStep P → jcx_EvenPeel P) ∧
      (jvp_VeblenStep jbc_Pce ∧ jvp_RegionStep jbc_Pce) ∧
      whc_FaithfulDiscreteJordan jbc_Pce :=
  ⟨fun P => jvp_evenPeel_of_steps P,
    ⟨jvp_veblenStep_unitSquare, jvp_regionStep_unitSquare⟩,
    jvp_faithfulDiscreteJordan_unitSquare⟩

end Lattice
end StatMech
