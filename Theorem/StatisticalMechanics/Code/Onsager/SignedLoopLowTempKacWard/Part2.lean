/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceClosure
import Def.StatisticalMechanics.Code.Onsager.SignedLoopLowTempKacWard.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

open StatMech.FrontierA

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

@[simp] theorem kwg_subdivExtract_lift (ends : E -> Sym2 V)
    (F : Finset E) :
    kwg_subdivExtract (kwg_subdivLift ends F) = F := by
  ext e
  simp [kwg_subdivExtract]


theorem kwg_subdivLift_extract_of_even (ends : E -> Sym2 V)
    (H : Finset (kwg_SubdivEdge V E))
    (hH : H ∈ evenSubgraphs (kwg_subdivGraph ends)) :
    kwg_subdivLift ends (kwg_subdivExtract H) = H := by
  have hdata := hH
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  ext edge
  constructor
  · intro hedge
    unfold kwg_subdivLift at hedge
    rw [Finset.mem_biUnion] at hedge
    obtain ⟨e, he, hedge⟩ := hedge
    have hc : kwg_subdivCentralEdge e ∈ H := by
      simpa [kwg_subdivExtract] using he
    simp only [kwg_subdivGadgetEdges, Finset.mem_insert,
      Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact (kwg_evenSubgraph_gadget_membership ends H hH e).mpr hc
    · exact hc
    · exact (kwg_evenSubgraph_gadget_membership_right ends H hH e).mpr hc
  · intro hedge
    have hedgeGraph := hdata.1 hedge
    rw [kwg_subdivGraph_mem_edgeFinset_iff] at hedgeGraph
    obtain ⟨e, he⟩ := hedgeGraph
    have hc : kwg_subdivCentralEdge e ∈ H := by
      simp only [kwg_subdivGadgetEdges, Finset.mem_insert,
        Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact (kwg_evenSubgraph_gadget_membership ends H hH e).mp hedge
      · exact hedge
      · exact (kwg_evenSubgraph_gadget_membership_right ends H hH e).mp hedge
    unfold kwg_subdivLift
    rw [Finset.mem_biUnion]
    exact ⟨e, by simp [kwg_subdivExtract, hc], he⟩

theorem kwg_subdivLeftEdge_injective (ends : E -> Sym2 V) :
    Function.Injective (kwg_subdivLeftEdge ends) := by
  intro e e' h
  unfold kwg_subdivLeftEdge at h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · simpa using congrArg (fun z => z.1) (Sum.inr.inj h.2)
  · simp at h

theorem kwg_subdivRightEdge_injective (ends : E -> Sym2 V) :
    Function.Injective (kwg_subdivRightEdge ends) := by
  intro e e' h
  unfold kwg_subdivRightEdge at h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · simpa using congrArg (fun z => z.1) (Sum.inr.inj h.1)
  · simp at h

@[simp] theorem kwg_subdivLeftEdge_mem_lift (ends : E -> Sym2 V)
    (F : Finset E) (e : E) :
    kwg_subdivLeftEdge ends e ∈ kwg_subdivLift ends F ↔ e ∈ F := by
  constructor
  · intro h
    unfold kwg_subdivLift at h
    rw [Finset.mem_biUnion] at h
    obtain ⟨e', he', hedge⟩ := h
    simp only [kwg_subdivGadgetEdges, Finset.mem_insert,
      Finset.mem_singleton] at hedge
    rcases hedge with hedge | hedge | hedge
    · exact (kwg_subdivLeftEdge_injective ends hedge).symm ▸ he'
    · unfold kwg_subdivLeftEdge kwg_subdivCentralEdge at hedge
      rw [Sym2.eq_iff] at hedge
      rcases hedge with h | h <;> simp at h
    · unfold kwg_subdivLeftEdge kwg_subdivRightEdge at hedge
      rw [Sym2.eq_iff] at hedge
      rcases hedge with h | h <;> simp at h
  · intro he
    unfold kwg_subdivLift
    rw [Finset.mem_biUnion]
    exact ⟨e, he, by simp [kwg_subdivGadgetEdges]⟩

@[simp] theorem kwg_subdivRightEdge_mem_lift (ends : E -> Sym2 V)
    (F : Finset E) (e : E) :
    kwg_subdivRightEdge ends e ∈ kwg_subdivLift ends F ↔ e ∈ F := by
  constructor
  · intro h
    unfold kwg_subdivLift at h
    rw [Finset.mem_biUnion] at h
    obtain ⟨e', he', hedge⟩ := h
    simp only [kwg_subdivGadgetEdges, Finset.mem_insert,
      Finset.mem_singleton] at hedge
    rcases hedge with hedge | hedge | hedge
    · unfold kwg_subdivRightEdge kwg_subdivLeftEdge at hedge
      rw [Sym2.eq_iff] at hedge
      rcases hedge with h | h <;> simp at h
    · unfold kwg_subdivRightEdge kwg_subdivCentralEdge at hedge
      rw [Sym2.eq_iff] at hedge
      rcases hedge with h | h <;> simp at h
    · exact (kwg_subdivRightEdge_injective ends hedge).symm ▸ he'
  · intro he
    unfold kwg_subdivLift
    rw [Finset.mem_biUnion]
    exact ⟨e, he, by simp [kwg_subdivGadgetEdges]⟩

theorem kwg_subdivLeft_right_disjoint (ends : E -> Sym2 V)
    (A B : Finset E) :
    Disjoint (A.image (kwg_subdivLeftEdge ends))
      (B.image (kwg_subdivRightEdge ends)) := by
  rw [Finset.disjoint_left]
  intro edge hleft hright
  rw [Finset.mem_image] at hleft hright
  obtain ⟨e, _, rfl⟩ := hleft
  obtain ⟨e', _, heq⟩ := hright
  unfold kwg_subdivLeftEdge kwg_subdivRightEdge at heq
  rw [Sym2.eq_iff] at heq
  rcases heq with h | h <;> simp at h

theorem kwg_incCount_subdivLift_face (ends : E -> Sym2 V)
    (F : Finset E) (v : V) :
    incCount (kwg_subdivLift ends F) (Sum.inl v) =
      (F.filter (fun e => (ends e).out.1 = v)).card +
        (F.filter (fun e => (ends e).out.2 = v)).card := by
  let A := F.filter (fun e => (ends e).out.1 = v)
  let B := F.filter (fun e => (ends e).out.2 = v)
  have hfilter :
      (kwg_subdivLift ends F).filter (fun edge => Sum.inl v ∈ edge) =
        A.image (kwg_subdivLeftEdge ends) ∪
          B.image (kwg_subdivRightEdge ends) := by
    ext edge
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hedge, hinc⟩
      unfold kwg_subdivLift at hedge
      rw [Finset.mem_biUnion] at hedge
      obtain ⟨e, heF, he⟩ := hedge
      simp only [kwg_subdivGadgetEdges, Finset.mem_insert,
        Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · left
        refine ⟨e, ?_, rfl⟩
        rw [Finset.mem_filter]
        refine ⟨heF, ?_⟩
        have hv : v = (ends e).out.1 := by
          simpa [kwg_subdivLeftEdge] using hinc
        exact hv.symm
      · simp [kwg_subdivCentralEdge] at hinc
      · right
        refine ⟨e, ?_, rfl⟩
        rw [Finset.mem_filter]
        refine ⟨heF, ?_⟩
        have hv : v = (ends e).out.2 := by
          simpa [kwg_subdivRightEdge] using hinc
        exact hv.symm
    · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
      · rw [Finset.mem_filter] at he
        constructor
        · unfold kwg_subdivLift
          rw [Finset.mem_biUnion]
          exact ⟨e, he.1, by simp [kwg_subdivGadgetEdges]⟩
        · simpa [kwg_subdivLeftEdge] using he.2.symm
      · rw [Finset.mem_filter] at he
        constructor
        · unfold kwg_subdivLift
          rw [Finset.mem_biUnion]
          exact ⟨e, he.1, by simp [kwg_subdivGadgetEdges]⟩
        · simpa [kwg_subdivRightEdge] using he.2.symm
  unfold incCount
  rw [hfilter, Finset.card_union_of_disjoint
    (kwg_subdivLeft_right_disjoint ends A B),
    Finset.card_image_of_injective _ (kwg_subdivLeftEdge_injective ends),
    Finset.card_image_of_injective _ (kwg_subdivRightEdge_injective ends)]

theorem kwg_subdivGraph_incident_false_iff (ends : E -> Sym2 V)
    (e : E) (edge : kwg_SubdivEdge V E) :
    edge ∈ (kwg_subdivGraph ends).edgeFinset ∧ Sum.inr (e, false) ∈ edge ↔
      edge = kwg_subdivLeftEdge ends e ∨ edge = kwg_subdivCentralEdge e := by
  induction edge using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rcases a with v | ⟨e', c⟩ <;> rcases b with w | ⟨e'', c'⟩
      · simp [kwg_subdivGraph, kwg_subdivLeftEdge,
          kwg_subdivCentralEdge, Sym2.eq_iff]
      · cases c' <;> simp [kwg_subdivGraph, kwg_subdivLeftEdge,
          kwg_subdivCentralEdge, Sym2.eq_iff, eq_comm] <;> grind
      · cases c <;> simp [kwg_subdivGraph, kwg_subdivLeftEdge,
          kwg_subdivCentralEdge, Sym2.eq_iff, eq_comm] <;> grind
      · cases c <;> cases c' <;> simp [kwg_subdivGraph,
          kwg_subdivLeftEdge, kwg_subdivCentralEdge, Sym2.eq_iff, eq_comm] <;> grind

theorem kwg_subdivGraph_incident_true_iff (ends : E -> Sym2 V)
    (e : E) (edge : kwg_SubdivEdge V E) :
    edge ∈ (kwg_subdivGraph ends).edgeFinset ∧ Sum.inr (e, true) ∈ edge ↔
      edge = kwg_subdivCentralEdge e ∨ edge = kwg_subdivRightEdge ends e := by
  induction edge using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rcases a with v | ⟨e', c⟩ <;> rcases b with w | ⟨e'', c'⟩
      · simp [kwg_subdivGraph, kwg_subdivCentralEdge,
          kwg_subdivRightEdge, Sym2.eq_iff]
      · cases c' <;> simp [kwg_subdivGraph, kwg_subdivCentralEdge,
          kwg_subdivRightEdge, Sym2.eq_iff, eq_comm] <;> grind
      · cases c <;> simp [kwg_subdivGraph, kwg_subdivCentralEdge,
          kwg_subdivRightEdge, Sym2.eq_iff, eq_comm] <;> grind
      · cases c <;> cases c' <;> simp [kwg_subdivGraph,
          kwg_subdivCentralEdge, kwg_subdivRightEdge, Sym2.eq_iff, eq_comm] <;> grind

theorem kwg_incCount_subdivLift_port (ends : E -> Sym2 V)
    (F : Finset E) (e : E) (b : Bool) :
    incCount (kwg_subdivLift ends F) (Sum.inr (e, b)) =
      if e ∈ F then 2 else 0 := by
  cases b
  · have hfilter :
        (kwg_subdivLift ends F).filter
            (fun edge => Sum.inr (e, false) ∈ edge) =
          if e ∈ F then
            {kwg_subdivLeftEdge ends e, kwg_subdivCentralEdge e} else ∅ := by
      ext edge
      by_cases he : e ∈ F
      · simp only [he, if_true, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hedge, hinc⟩
          exact (kwg_subdivGraph_incident_false_iff ends e edge).mp
            ⟨kwg_subdivLift_subset_edgeFinset ends F hedge, hinc⟩
        · intro hedge
          rcases hedge with rfl | rfl
          · exact ⟨by
                unfold kwg_subdivLift
                rw [Finset.mem_biUnion]
                exact ⟨e, he, by simp [kwg_subdivGadgetEdges]⟩,
              by simp [kwg_subdivLeftEdge]⟩
          · exact ⟨by
                unfold kwg_subdivLift
                rw [Finset.mem_biUnion]
                exact ⟨e, he, by simp [kwg_subdivGadgetEdges]⟩,
              by simp [kwg_subdivCentralEdge]⟩
      · rw [if_neg he]
        rw [Finset.mem_filter]
        rw [show edge ∈ (∅ : Finset (kwg_SubdivEdge V E)) ↔ False by simp]
        rw [iff_false]
        rintro ⟨hedge, hinc⟩
        have hcases := (kwg_subdivGraph_incident_false_iff ends e edge).mp
          ⟨kwg_subdivLift_subset_edgeFinset ends F hedge, hinc⟩
        rcases hcases with rfl | rfl
        · exact he ((kwg_subdivLeftEdge_mem_lift ends F e).mp hedge)
        · exact he ((kwg_subdivCentralEdge_mem_lift ends F e).mp hedge)
    unfold incCount
    rw [hfilter]
    split_ifs with he
    · simp [kwg_subdivLeftEdge, kwg_subdivCentralEdge, Sym2.eq_iff]
    · rfl
  · have hfilter :
        (kwg_subdivLift ends F).filter
            (fun edge => Sum.inr (e, true) ∈ edge) =
          if e ∈ F then
            {kwg_subdivCentralEdge e, kwg_subdivRightEdge ends e} else ∅ := by
      ext edge
      by_cases he : e ∈ F
      · simp only [he, if_true, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hedge, hinc⟩
          exact (kwg_subdivGraph_incident_true_iff ends e edge).mp
            ⟨kwg_subdivLift_subset_edgeFinset ends F hedge, hinc⟩
        · intro hedge
          rcases hedge with rfl | rfl
          · exact ⟨by
                unfold kwg_subdivLift
                rw [Finset.mem_biUnion]
                exact ⟨e, he, by simp [kwg_subdivGadgetEdges]⟩,
              by simp [kwg_subdivCentralEdge]⟩
          · exact ⟨by
                unfold kwg_subdivLift
                rw [Finset.mem_biUnion]
                exact ⟨e, he, by simp [kwg_subdivGadgetEdges]⟩,
              by simp [kwg_subdivRightEdge]⟩
      · rw [if_neg he]
        rw [Finset.mem_filter]
        rw [show edge ∈ (∅ : Finset (kwg_SubdivEdge V E)) ↔ False by simp]
        rw [iff_false]
        rintro ⟨hedge, hinc⟩
        have hcases := (kwg_subdivGraph_incident_true_iff ends e edge).mp
          ⟨kwg_subdivLift_subset_edgeFinset ends F hedge, hinc⟩
        rcases hcases with rfl | rfl
        · exact he ((kwg_subdivCentralEdge_mem_lift ends F e).mp hedge)
        · exact he ((kwg_subdivRightEdge_mem_lift ends F e).mp hedge)
    unfold incCount
    rw [hfilter]
    split_ifs with he
    · simp [kwg_subdivCentralEdge, kwg_subdivRightEdge, Sym2.eq_iff]
    · rfl

theorem kwg_subdiv_card_filter_eq_sum_ite
    (F : Finset E) (p : E -> Prop) [DecidablePred p] :
    (F.filter p).card = ∑ e ∈ F, if p e then 1 else 0 := by
  induction F using Finset.induction with
  | empty => simp
  | @insert e F he ih =>
      by_cases hp : p e <;> simp [he, hp, ih]

theorem kwg_endpointCount_even_iff (ends : E -> Sym2 V)
    (F : Finset E) (v : V) :
    Even ((F.filter (fun e => (ends e).out.1 = v)).card +
      (F.filter (fun e => (ends e).out.2 = v)).card) ↔
      Even (kwg_degree ends F v) := by
  let A := F.filter (fun e => (ends e).out.1 = v)
  let B := F.filter (fun e => (ends e).out.2 = v)
  let I := F.filter (fun e => kwg_incidentMod2 v (ends e))
  let L := F.filter
    (fun e => (ends e).out.1 = v ∧ (ends e).out.2 = v)
  have hcount : A.card + B.card = I.card + 2 * L.card := by
    rw [kwg_subdiv_card_filter_eq_sum_ite,
      kwg_subdiv_card_filter_eq_sum_ite,
      kwg_subdiv_card_filter_eq_sum_ite,
      kwg_subdiv_card_filter_eq_sum_ite]
    rw [← Finset.sum_add_distrib]
    calc
      ∑ e ∈ F, ((if (ends e).out.1 = v then 1 else 0) +
          if (ends e).out.2 = v then 1 else 0) =
          ∑ e ∈ F, ((if kwg_incidentMod2 v (ends e) then 1 else 0) +
            2 * if (ends e).out.1 = v ∧ (ends e).out.2 = v then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro e _
        have hout : ends e = s((ends e).out.1, (ends e).out.2) :=
          (ends e).out_eq.symm
        have hinc : kwg_incidentMod2 v (ends e) ↔
            ((ends e).out.1 = v ∧ (ends e).out.2 ≠ v) ∨
              ((ends e).out.2 = v ∧ (ends e).out.1 ≠ v) := by
          conv_lhs => rw [hout]
          exact kwg_incidentMod2_mk v (ends e).out.1 (ends e).out.2
        by_cases h1 : (ends e).out.1 = v <;>
          by_cases h2 : (ends e).out.2 = v <;> simp [hinc, h1, h2]
      _ = (∑ e ∈ F, if kwg_incidentMod2 v (ends e) then 1 else 0) +
          ∑ e ∈ F, 2 * if (ends e).out.1 = v ∧
            (ends e).out.2 = v then 1 else 0 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ e ∈ F, if kwg_incidentMod2 v (ends e) then 1 else 0) +
          2 * ∑ e ∈ F, if (ends e).out.1 = v ∧
            (ends e).out.2 = v then 1 else 0 := by
        rw [Finset.mul_sum]
  change Even (A.card + B.card) ↔ Even I.card
  rw [hcount]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - L.card, ?_⟩
    omega
  · rintro ⟨k, hk⟩
    refine ⟨k + L.card, ?_⟩
    omega


theorem kwg_subdivLift_isEven_iff (ends : E -> Sym2 V) (F : Finset E) :
    IsEvenSubgraph (kwg_subdivLift ends F) ↔ kwg_IsEven ends F := by
  constructor
  · intro h v
    have hv := h (Sum.inl v)
    rw [kwg_incCount_subdivLift_face] at hv
    exact (kwg_endpointCount_even_iff ends F v).mp hv
  · intro h z
    rcases z with v | ⟨e, b⟩
    · rw [kwg_incCount_subdivLift_face]
      exact (kwg_endpointCount_even_iff ends F v).mpr (h v)
    · rw [kwg_incCount_subdivLift_port]
      split_ifs <;> norm_num

theorem kwg_subdivLift_mem_evenSubgraphs_iff (ends : E -> Sym2 V)
    (F : Finset E) :
    kwg_subdivLift ends F ∈ evenSubgraphs (kwg_subdivGraph ends) ↔
      kwg_IsEven ends F := by
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
  exact and_iff_right (kwg_subdivLift_subset_edgeFinset ends F) |>.trans
    (kwg_subdivLift_isEven_iff ends F)


end
end StatMech.Onsager
