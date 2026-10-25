/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.TrivalentCycles
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.Onsager.TorusDecoration.Part7


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

theorem ons_incidenceFinset_eq_image_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) :
    H.incidenceFinset v = (H.neighborFinset v).image (fun w => s(v, w)) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      simp only [SimpleGraph.mem_incidenceFinset,
        SimpleGraph.mk'_mem_incidenceSet_iff, Finset.mem_image,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hab, rfl | rfl⟩
        · exact ⟨b, hab, rfl⟩
        · exact ⟨a, hab.symm, Sym2.eq_swap⟩
      · rintro ⟨w, hvw, heq⟩
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨hva, hwb⟩ | ⟨hvb, hwa⟩
        · subst a
          subst b
          exact ⟨hvw, Or.inl rfl⟩
        · subst a
          subst b
          exact ⟨hvw.symm, Or.inr rfl⟩

theorem ons_neighborEdge_injective
    {V : Type*} [DecidableEq V] (H : SimpleGraph V) (v : V) :
    Set.InjOn (fun w => s(v, w)) (H.neighborSet v) := by
  intro a ha b hb heq
  rw [Sym2.eq_iff] at heq
  rcases heq with h | h
  · exact h.2
  · exfalso
    have hva : H.Adj v a := ha
    rw [h.2] at hva
    exact H.loopless.irrefl v hva

theorem ons_incCount_filter_edgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (Q : Sym2 V → Prop) [DecidablePred Q] (v : V) :
    incCount (H.edgeFinset.filter Q) v =
      ((H.incidenceFinset v).filter Q).card := by
  unfold incCount
  rw [SimpleGraph.incidenceFinset_eq_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  tauto

theorem ons_cast_incCount_filter_eq_neighbor_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (Q : Sym2 V → Prop) [DecidablePred Q] (v : V) :
    ((incCount (H.edgeFinset.filter Q) v : ℕ) : ZMod 2) =
      ∑ w ∈ H.neighborFinset v,
        if Q s(v, w) then (1 : ZMod 2) else 0 := by
  rw [ons_incCount_filter_edgeFinset, Finset.natCast_card_filter,
    ons_incidenceFinset_eq_image_neighborFinset, Finset.sum_image]
  intro a ha b hb hab
  apply ons_neighborEdge_injective H v
  · exact (SimpleGraph.mem_neighborFinset H v a).mp ha
  · exact (SimpleGraph.mem_neighborFinset H v b).mp hb
  · exact hab

theorem ons_evenSubgraph_neighbor_sum_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (F : Finset (Sym2 V)) (hF : F ∈ evenSubgraphs H) (v : V) :
    ∑ w ∈ H.neighborFinset v,
      (if s(v, w) ∈ F then (1 : ZMod 2) else 0) = 0 := by
  have hdata := hF
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  have hFeq : F = H.edgeFinset.filter (fun e => e ∈ F) := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · intro he
      exact ⟨hdata.1 he, he⟩
    · exact And.right
  have hcast : ((incCount F v : ℕ) : ZMod 2) = 0 := by
    apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mpr
    exact even_iff_two_dvd.mp (hdata.2 v)
  have hsum := ons_cast_incCount_filter_eq_neighbor_sum H (fun e => e ∈ F) v
  rw [← hFeq, hcast] at hsum
  exact hsum.symm

@[simp] theorem ons_fin2_indicator_eq (a : Fin 2) :
    (if a = 1 then (1 : Fin 2) else 0) = a := by
  fin_cases a <;> decide

theorem ons_dirStep_ne_self (L : ℕ) [Fact (2 < L)]
    (mu : Fin 4) (s : ZMod L × ZMod L) :
    ons_dirStep L mu s ≠ s := by
  haveI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero
  fin_cases mu <;> simp [ons_dirStep, Prod.ext_iff, h1]

theorem ons_decInternalNeighbors_site {L : ℕ} {d e : ons_Dart L}
    (he : e ∈ ons_decInternalNeighbors d) : e.1 = d.1 := by
  rcases d with ⟨s, mu⟩
  fin_cases mu <;> simp [ons_decInternalNeighbors] at he <;>
    rcases he with rfl | rfl <;> rfl

theorem ons_dartRev_not_mem_internalNeighbors (L : ℕ) [Fact (2 < L)]
    (d : ons_Dart L) :
    ons_dartRev L d ∉ ons_decInternalNeighbors d := by
  intro h
  have hsite : (ons_dartRev L d).1 = d.1 := ons_decInternalNeighbors_site h
  exact ons_dirStep_ne_self L d.2 d.1 hsite


theorem ons_decNeighborBit_sum_zero (L : ℕ) [Fact (2 < L)]
    (P : ons_PortPattern L) (d : ons_Dart L) :
    ∑ e ∈ (ons_decGraph L).neighborFinset d, ons_decNeighborBit P d e = 0 := by
  rw [ons_decGraph_neighborFinset,
    Finset.sum_insert (ons_dartRev_not_mem_internalNeighbors L d)]
  have hchain := (ons_decChainCompletion_even_iff
    (P.bit (d.1, 0)) (P.bit (d.1, 1))
    (P.bit (d.1, 2)) (P.bit (d.1, 3))).mpr (P.site_even d.1)
  unfold ons_decChainEven at hchain
  rcases d with ⟨s, mu⟩
  fin_cases mu
  · simpa [ons_decNeighborBit, ons_decInternalNeighbors, ons_portChainBit,
      ons_dartRev] using hchain.1
  · simpa [ons_decNeighborBit, ons_decInternalNeighbors, ons_portChainBit,
      ons_dartRev, add_assoc] using hchain.2.1
  · simpa [ons_decNeighborBit, ons_decInternalNeighbors, ons_portChainBit,
      ons_dartRev, add_assoc] using hchain.2.2.1
  · simpa [ons_decNeighborBit, ons_decInternalNeighbors, ons_portChainBit,
      ons_dartRev] using hchain.2.2.2


end StatMech.Onsager
