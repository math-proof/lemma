/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Def.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem mem_notConnComp {m : Current V} {g v : V} :
    v ∈ notConnComp G m g ↔ ¬ CurrentConnected G m g v := by
  classical simp [notConnComp]


theorem noCrossing_of_event (m : Current V) (S : Finset V) (g : V) (_hg : g ∉ S)
    (hev : notConnComp G m g = S) : NoCrossing G m S := by
  intro e he hpos
  obtain ⟨⟨u, v⟩, huv⟩ := e.exists_rep
  subst huv
  have hadj : G.Adj u v := by rw [mem_edgeFinset, mem_edgeSet] at he; exact he
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
  · left; intro w hw; rw [Sym2.mem_iff] at hw; rcases hw with rfl | rfl <;> assumption
  · 
    exfalso
    have hconn_uv : CurrentConnected G m u v := Adj.reachable ⟨hadj, hpos⟩
    have hvconn : CurrentConnected G m g v := by
      by_contra hc; exact hv (hev ▸ (mem_notConnComp G).mpr hc)
    have huconn : CurrentConnected G m g u := SimpleGraph.Reachable.trans hvconn hconn_uv.symm
    exact ((mem_notConnComp G).not.mpr (not_not.mpr huconn)) (hev ▸ hu)
  · 
    exfalso
    have hconn_uv : CurrentConnected G m v u :=
      Adj.reachable ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
    have huconn : CurrentConnected G m g u := by
      by_contra hc; exact hu (hev ▸ (mem_notConnComp G).mpr hc)
    have hvconn : CurrentConnected G m g v := SimpleGraph.Reachable.trans huconn hconn_uv.symm
    exact ((mem_notConnComp G).not.mpr (not_not.mpr hvconn)) (hev ▸ hv)
  · right; intro w hw; rw [Finset.mem_compl]; rw [Sym2.mem_iff] at hw
    rcases hw with rfl | rfl <;> assumption


theorem currentSubgraph_restrictCompl_congr (m m' : Current V) (S : Finset V)
    (hagree : ∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) :
    currentSubgraph G (restrictTo m Sᶜ) = currentSubgraph G (restrictTo m' Sᶜ) := by
  ext u v
  simp only [currentSubgraph_adj, restrictTo_apply]
  constructor <;> rintro ⟨hadj, hpos⟩ <;> refine ⟨hadj, ?_⟩ <;>
    by_cases hc : edgeInside Sᶜ s(u, v)
  · rw [if_pos hc] at hpos ⊢
    have he : s(u, v) ∈ G.edgeFinset := by rw [mem_edgeFinset, mem_edgeSet]; exact hadj
    rw [← hagree _ he (fun hi => not_edgeInside_compl_of_edgeInside S _ hi hc)]; exact hpos
  · rw [if_neg hc] at hpos; omega
  · rw [if_pos hc] at hpos ⊢
    have he : s(u, v) ∈ G.edgeFinset := by rw [mem_edgeFinset, mem_edgeSet]; exact hadj
    rw [hagree _ he (fun hi => not_edgeInside_compl_of_edgeInside S _ hi hc)]; exact hpos
  · rw [if_neg hc] at hpos; omega


theorem noCrossing_congr (m m' : Current V) (S : Finset V) (hnm : NoCrossing G m S)
    (hagree : ∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) :
    NoCrossing G m' S := by
  intro e he hpos
  by_cases hi : edgeInside S e
  · exact Or.inl hi
  · have hmpos : 1 ≤ m e := by rw [hagree e he hi]; exact hpos
    rcases hnm e he hmpos with h | h
    · exact absurd h hi
    · exact Or.inr h


theorem notConnComp_congr (m m' : Current V) (S : Finset V) (g : V) (hg : g ∉ S)
    (hev : notConnComp G m g = S)
    (hagree : ∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) :
    notConnComp G m' g = S := by
  have hnm : NoCrossing G m S := noCrossing_of_event G m S g hg hev
  have hnm' : NoCrossing G m' S := noCrossing_congr G m m' S hnm hagree
  have hsub := currentSubgraph_restrictCompl_congr G m m' S hagree
  rw [← hev]
  ext v
  rw [mem_notConnComp, mem_notConnComp]
  by_cases hv : v ∈ S
  · constructor <;> intro _
    · exact not_currentConnected_in_S G m S hnm g hg v (hev ▸ hv)
    · exact not_currentConnected_in_S G m' S hnm' g hg v (hev ▸ hv)
  · rw [currentConnected_iff_compl G m' S hnm' g v hg,
      currentConnected_iff_compl G m S hnm g v hg]
    unfold CurrentConnected
    rw [hsub]


theorem claim2_ising (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (g : V) (hg : g ∉ S)
    (zero x : V) (h0 : zero ∈ S) (hx : x ∈ S)
    (hZ : currentSum G β (couplingIn J S) ∅ ≠ 0) :
    (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
        (if sources G (ofEdgeFun G pq.1) = {zero, x} then weight G β J (ofEdgeFun G pq.1) else 0)
          * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
          * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S
              then 1 else 0))
    = expectationJ G β (couplingIn J S) {zero, x}
      * (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
          (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
            * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S
                then 1 else 0)) := by
  classical
  exact claim2_abstract G β J S (fun m => notConnComp G m g = S)
    (fun m hm => noCrossing_of_event G m S g hg hm)
    (fun m m' hagree => ⟨fun hm => notConnComp_congr G m m' S g hg hm hagree,
      fun hm' => notConnComp_congr G m' m S g hg hm' (fun i hi hni => (hagree i hi hni).symm)⟩)
    zero x h0 hx hZ

end Sharpness
end StatMech
