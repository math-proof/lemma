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
import Def.StatisticalMechanics.Code.Onsager.TorusDecoration.Part11


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

theorem ons_portEdge_mem_portPatternEdges_iff (L : ℕ) [Fact (2 < L)]
    (P : ons_PortPattern L) (d : ons_Dart L) :
    ons_portEdge L d ∈ ons_portPatternEdges L P ↔ P.bit d = 1 := by
  rw [ons_portPatternEdges, Finset.mem_image]
  constructor
  · rintro ⟨e, he, hedge⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases (ons_portEdge_eq_iff L d e).mp hedge with rfl | rfl
    · exact he
    · simpa only [P.rev_bit] using he
  · intro hd
    exact ⟨d, by simp [hd], rfl⟩

theorem ons_torusEdge_eq_portEdge (L : ℕ) [Fact (2 < L)]
    {edge : Sym2 (ZMod L × ZMod L)}
    (hedge : edge ∈ (onsTorusGraph L).edgeFinset) :
    ∃ d : ons_Dart L, ons_portEdge L d = edge := by
  induction edge using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        ← SimpleGraph.mem_neighborFinset, ons_torus_neighborFinset_steps] at hedge
      simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
      rcases hedge with rfl | rfl | rfl | rfl
      · exact ⟨(u, 0), rfl⟩
      · exact ⟨(u, 1), rfl⟩
      · exact ⟨(u, 2), rfl⟩
      · exact ⟨(u, 3), rfl⟩

theorem ons_portPatternEdges_subset (L : ℕ) [Fact (2 < L)]
    (P : ons_PortPattern L) :
    ons_portPatternEdges L P ⊆ (onsTorusGraph L).edgeFinset := by
  intro edge hedge
  rw [ons_portPatternEdges, Finset.mem_image] at hedge
  rcases hedge with ⟨d, _, rfl⟩
  exact ons_portEdge_mem_edgeFinset L d

theorem ons_portPatternEdges_even (L : ℕ) [Fact (2 < L)]
    (P : ons_PortPattern L) :
    ons_portPatternEdges L P ∈ evenSubgraphs (onsTorusGraph L) := by
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact ons_portPatternEdges_subset L P
  · intro v
    apply even_iff_two_dvd.mpr
    apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp
    have hFeq : ons_portPatternEdges L P =
        (onsTorusGraph L).edgeFinset.filter
          (fun e => e ∈ ons_portPatternEdges L P) := by
      ext e
      simp only [Finset.mem_filter]
      constructor
      · intro he
        exact ⟨ons_portPatternEdges_subset L P he, he⟩
      · exact And.right
    have hsum := ons_cast_incCount_filter_eq_neighbor_sum
      (onsTorusGraph L) (fun e => e ∈ ons_portPatternEdges L P) v
    rw [← hFeq, ons_torus_neighbor_sum_eq_direction_sum] at hsum
    have hind : ∀ mu : Fin 4,
        (if s(v, ons_dirStep L mu v) ∈ ons_portPatternEdges L P
          then (1 : ZMod 2) else 0) = P.bit (v, mu) := by
      intro mu
      change (if ons_portEdge L (v, mu) ∈ ons_portPatternEdges L P
        then (1 : Fin 2) else 0) = P.bit (v, mu)
      simp only [ons_portEdge_mem_portPatternEdges_iff]
      exact ons_fin2_indicator_eq _
    simp_rw [hind] at hsum
    rw [Fin.sum_univ_four] at hsum
    have hp : (P.bit (v, 0) : ZMod 2) + P.bit (v, 1) +
        P.bit (v, 2) + P.bit (v, 3) = 0 := by
      exact_mod_cast P.site_even v
    exact hsum.trans hp

theorem ons_portPatternEdges_evenSubgraphPortPattern
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
    ons_portPatternEdges L (ons_evenSubgraphPortPattern L F hF) = F := by
  ext edge
  constructor
  · intro hedge
    rw [ons_portPatternEdges, Finset.mem_image] at hedge
    rcases hedge with ⟨d, hd, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ons_evenSubgraphPortPattern, ons_portBit] at hd
    split at hd
    · assumption
    · simp at hd
  · intro hedge
    have hdata := hF
    rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
    obtain ⟨d, hd⟩ := ons_torusEdge_eq_portEdge L (hdata.1 hedge)
    rw [← hd]
    rw [ons_portEdge_mem_portPatternEdges_iff]
    simp [ons_evenSubgraphPortPattern, ons_portBit, hd, hedge]

theorem ons_evenSubgraphPortPattern_portPatternEdges
    (L : ℕ) [Fact (2 < L)] (P : ons_PortPattern L) :
    ons_evenSubgraphPortPattern L (ons_portPatternEdges L P)
      (ons_portPatternEdges_even L P) = P := by
  apply ons_PortPattern.ext
  funext d
  simp [ons_evenSubgraphPortPattern, ons_portBit,
    ons_portEdge_mem_portPatternEdges_iff, ons_fin2_indicator_eq]


end StatMech.Onsager
