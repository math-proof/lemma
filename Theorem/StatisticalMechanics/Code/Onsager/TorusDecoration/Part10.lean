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
import Def.StatisticalMechanics.Code.Onsager.TorusDecoration.Part10


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

theorem ons_decoratedChainBits_eq_completion (L : ℕ) [Fact (2 < L)]
    (D : Finset (Sym2 (ons_Dart L)))
    (hD : D ∈ evenSubgraphs (ons_decGraph L))
    (s : ZMod L × ZMod L) :
    ons_decoratedChainBits D s =
      ons_portChainBit (ons_portPatternOfDecorated L D hD) s := by
  apply ons_decChain_eq_completion
  · exact (ons_portPatternOfDecorated L D hD).site_even s
  · exact ons_decorated_local_even L D hD s


theorem ons_decoratedEdges_portPatternOfDecorated (L : ℕ) [Fact (2 < L)]
    (D : Finset (Sym2 (ons_Dart L)))
    (hD : D ∈ evenSubgraphs (ons_decGraph L)) :
    ons_decoratedEdges (ons_portPatternOfDecorated L D hD) = D := by
  have hdata := hD
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  ext edge
  induction edge using Sym2.inductionOn with
  | _ d e =>
      by_cases hedge : s(d, e) ∈ (ons_decGraph L).edgeFinset
      · have hadj : ons_decAdj L d e := by
          exact SimpleGraph.mem_edgeFinset.mp hedge
        rcases hadj with hrev | hint
        · subst e
          rw [ons_decoratedEdges, Finset.mem_filter, and_iff_right hedge,
            ons_decEdgeBit_mk, ons_decNeighborBit, if_pos rfl]
          change ons_decoratedPortBit D d = 1 ↔
            s(d, ons_dartRev L d) ∈ D
          simp [ons_decoratedPortBit]
        · rcases d with ⟨s, mu⟩
          rcases e with ⟨t, nu⟩
          rcases hint with ⟨hsite, hdir⟩
          change s = t at hsite
          subst t
          have hne : (s, nu) ≠ ons_dartRev L (s, mu) := by
            intro h
            have hs := congrArg Prod.fst h
            exact ons_dirStep_ne_self L mu s hs.symm
          rw [ons_decoratedEdges, Finset.mem_filter, and_iff_right hedge,
            ons_decEdgeBit_mk, ons_decNeighborBit, if_neg hne, if_pos rfl]
          have hchain := ons_decoratedChainBits_eq_completion L D hD s
          have hc0 := congrFun hchain 0
          have hc1 := congrFun hchain 1
          have hc2 := congrFun hchain 2
          have hc0f :
              (if s((s, 0), (s, 1)) ∈ D then (1 : Fin 2) else 0) =
                ons_portChainBit (ons_portPatternOfDecorated L D hD) s 0 := by
            simpa [ons_decoratedChainBits] using hc0
          have hc1f :
              (if s((s, 1), (s, 2)) ∈ D then (1 : Fin 2) else 0) =
                ons_portChainBit (ons_portPatternOfDecorated L D hD) s 1 := by
            simpa [ons_decoratedChainBits] using hc1
          have hc2f :
              (if s((s, 2), (s, 3)) ∈ D then (1 : Fin 2) else 0) =
                ons_portChainBit (ons_portPatternOfDecorated L D hD) s 2 := by
            simpa [ons_decoratedChainBits] using hc2
          have hc0r :
              (if s((s, 1), (s, 0)) ∈ D then (1 : Fin 2) else 0) =
                ons_portChainBit (ons_portPatternOfDecorated L D hD) s 0 := by
            rw [show s((s, (1 : Fin 4)), (s, (0 : Fin 4))) =
              s((s, (0 : Fin 4)), (s, (1 : Fin 4))) from Sym2.eq_swap]
            exact hc0
          have hc1r :
              (if s((s, 2), (s, 1)) ∈ D then (1 : Fin 2) else 0) =
                ons_portChainBit (ons_portPatternOfDecorated L D hD) s 1 := by
            rw [show s((s, (2 : Fin 4)), (s, (1 : Fin 4))) =
              s((s, (1 : Fin 4)), (s, (2 : Fin 4))) from Sym2.eq_swap]
            exact hc1
          have hc2r :
              (if s((s, 3), (s, 2)) ∈ D then (1 : Fin 2) else 0) =
                ons_portChainBit (ons_portPatternOfDecorated L D hD) s 2 := by
            rw [show s((s, (3 : Fin 4)), (s, (2 : Fin 4))) =
              s((s, (2 : Fin 4)), (s, (3 : Fin 4))) from Sym2.eq_swap]
            exact hc2
          have hind {p : Prop} [Decidable p] {a : Fin 2}
              (h : (if p then (1 : Fin 2) else 0) = a) : a = 1 ↔ p := by
            rw [← h]
            simp
          fin_cases mu <;> fin_cases nu <;>
            simp [ons_decInternalAdj] at hdir <;>
            first
            | exact hind hc0f
            | exact hind hc0r
            | exact hind hc1f
            | exact hind hc1r
            | exact hind hc2f
            | exact hind hc2r
      · have hnotD : s(d, e) ∉ D := fun he => hedge (hdata.1 he)
        simp [ons_decoratedEdges, hedge, hnotD]

@[simp] theorem ons_decEdgeBit_external {L : ℕ} (P : ons_PortPattern L)
    (d : ons_Dart L) :
    ons_decEdgeBit P s(d, ons_dartRev L d) = P.bit d := by
  rw [ons_decEdgeBit_mk, ons_decNeighborBit, if_pos rfl]

theorem ons_decorated_external_mem_iff (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L)) (d : ons_Dart L) :
    s(d, ons_dartRev L d) ∈
        ons_decoratedEdges (ons_evenSubgraphPortPattern L F hF) ↔
      ons_portEdge L d ∈ F := by
  rw [ons_decoratedEdges, Finset.mem_filter]
  have hedge : s(d, ons_dartRev L d) ∈ (ons_decGraph L).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact Or.inl rfl
  rw [and_iff_right hedge, ons_decEdgeBit_external]
  change ons_portBit F d = 1 ↔ ons_portEdge L d ∈ F
  simp [ons_portBit]

theorem ons_decoratedEdges_even (L : ℕ) [Fact (2 < L)]
    (P : ons_PortPattern L) :
    ons_decoratedEdges P ∈ evenSubgraphs (ons_decGraph L) := by
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact Finset.filter_subset _ _
  · intro d
    apply even_iff_two_dvd.mpr
    apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp
    rw [ons_decoratedEdges]
    rw [ons_incCount_filter_edgeFinset]
    rw [Finset.natCast_card_filter]
    have hind : ∀ e : Sym2 (ons_Dart L),
        (if ons_decEdgeBit P e = 1 then (1 : ZMod 2) else 0) =
          ons_decEdgeBit P e := by
      intro e
      generalize heq : ons_decEdgeBit P e = a
      fin_cases a <;> simp_all <;> rfl
    simp_rw [hind]
    rw [ons_incidenceFinset_eq_image_neighborFinset]
    rw [Finset.sum_image]
    · simpa only [ons_decEdgeBit_mk] using ons_decNeighborBit_sum_zero L P d
    · intro a ha b hb hab
      apply ons_neighborEdge_injective (ons_decGraph L) d
      · exact (SimpleGraph.mem_neighborFinset (ons_decGraph L) d a).mp ha
      · exact (SimpleGraph.mem_neighborFinset (ons_decGraph L) d b).mp hb
      · exact hab


theorem ons_portEdge_mem_edgeFinset (L : ℕ) [Fact (2 < L)]
    (d : ons_Dart L) :
    ons_portEdge L d ∈ (onsTorusGraph L).edgeFinset := by
  rcases d with ⟨v, mu⟩
  rw [SimpleGraph.mem_edgeFinset]
  simp only [ons_portEdge]
  rw [SimpleGraph.mem_edgeSet]
  change (onsTorusGraph L).Adj v (ons_dirStep L mu v)
  rw [← SimpleGraph.mem_neighborFinset, ons_torus_neighborFinset_steps]
  fin_cases mu <;> simp


theorem ons_portEdge_eq_iff (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L) :
    ons_portEdge L e = ons_portEdge L d ↔
      e = d ∨ e = ons_dartRev L d := by
  rcases d with ⟨u, mu⟩
  rcases e with ⟨v, nu⟩
  constructor
  · intro h
    simp only [ons_portEdge, Sym2.eq_iff] at h
    rcases h with ⟨hvu, hstep⟩ | ⟨hvstep, hstepu⟩
    · subst v
      have hmu : nu = mu := ons_dirStep_injective L u hstep
      subst nu
      exact Or.inl rfl
    · have hnu : nu = mu + 2 := by
        apply ons_dirStep_injective L v
        calc
          ons_dirStep L nu v = u := hstepu
          _ = ons_dirStep L (mu + 2) v := by
            rw [hvstep, ons_dirStep_opposite]
      right
      simp only [ons_dartRev, Prod.mk.injEq]
      exact ⟨hvstep, hnu⟩
  · intro h
    rcases h with h | h
    · cases h
      rfl
    · cases h
      exact ons_portEdge_rev L (u, mu)


end StatMech.Onsager
