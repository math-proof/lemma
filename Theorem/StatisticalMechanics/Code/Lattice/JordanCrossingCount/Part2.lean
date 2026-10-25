/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanGeneralCount.Part5
import Inductive.StatisticalMechanics.Code.Lattice.JordanCrossingCount
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jcx_tc_eq_faceCount (P : PlanarZ2Subgraph) :
    ∀ {K : SimpleGraph P.V}, jcx_IsEvenPeelable K → K ≤ P.G → jic_tc P K = faceCount K := by
  classical
  haveI : Finite P.V := P.finV
  haveI : DecidableEq P.V := P.decV
  intro K hpe
  induction hpe with
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
  | @cycle K hev v p hp hiso hrec ih =>
    intro hKle
    haveI hlfK : SimpleGraph.LocallyFinite K := fun w => Fintype.ofFinite _
    haveI hdec : DecidableRel K.Adj := Classical.decRel _
    have hK'le : K.deleteEdges p.toSubgraph.edgeSet ≤ P.G := (deleteEdges_le _).trans hKle
    have ihK' := ih hK'le
    have hreg := jcx_tc_deleteCycle P K hKle hev p hp hiso
    have hface := jcx_faceCount_deleteCycle K p hp hiso
    rw [hreg, ihK']; omega


theorem jcx_total_count (P : PlanarZ2Subgraph) (hpe : jcx_IsEvenPeelable P.G) :
    Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = faceCount P.G := by
  have h := jcx_tc_eq_faceCount P hpe le_rfl
  unfold jic_tc at h
  rwa [jei_pushGraph_G P] at h


theorem jcx_faithfulRegionCount_eq_nullity (P : PlanarZ2Subgraph) (hpe : jcx_IsEvenPeelable P.G) :
    whc_faithfulRegionCount P = nullity P.G := by
  have htot := jcx_total_count P hpe
  have hcard := jfc_whb_bounded_add_one_eq_card P
  rw [htot, faceCount] at hcard
  omega


theorem jcx_faithfulDiscreteJordan (P : PlanarZ2Subgraph) (hpe : jcx_IsEvenPeelable P.G) :
    whc_FaithfulDiscreteJordan P := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph P)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph P) (Set.toFinite (imageGraph P).edgeSet)
  have heq : whc_faithfulRegionCount P = nullity P.G :=
    jcx_faithfulRegionCount_eq_nullity P hpe
  unfold whc_faithfulRegionCount at heq
  exact ⟨Finite.equivFinOfCardEq heq⟩


theorem jcx_cycleVerts_isolated {V : Type*} [Finite V] [DecidableEq V] {K : SimpleGraph V}
    [LocallyFinite K] (hcyc : K.IsCycles) {v : V} (p : K.Walk v v) (hp : p.IsCycle) :
    ∀ u ∈ p.support, ∀ w, ¬ (K.deleteEdges p.toSubgraph.edgeSet).Adj u w := by
  intro u hu w hadjw
  rw [deleteEdges_adj] at hadjw
  obtain ⟨hKadj, hnotin⟩ := hadjw
  have huv : u ∈ p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr hu
  have := (hp.adj_toSubgraph_iff_of_isCycles hcyc huv w).mpr hKadj
  exact hnotin (by rw [Subgraph.mem_edgeSet]; exact this)


theorem jcx_isEvenPeelable_of_isCycles {V : Type*} [Finite V] [DecidableEq V]
    (K : SimpleGraph V) (hcyc : K.IsCycles) : jcx_IsEvenPeelable K := by
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
      subst hbot; exact jcx_IsEvenPeelable.bot
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
      have hiso : ∀ u ∈ p.support, u ≠ a →
          ∀ w, ¬ (K.deleteEdges p.toSubgraph.edgeSet).Adj u w :=
        fun u hu _ w => jcx_cycleVerts_isolated hcyc p hpc u hu w
      exact jcx_IsEvenPeelable.cycle (jcx_isEven_of_isCycles hcyc) p hpc hiso
        (ih _ (by omega) _ hK'cyc rfl)


end Lattice
end StatMech
