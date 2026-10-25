/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part11


namespace StatMech.Onsager

theorem ons_mem_decDartSegment_iff
    (L : ℕ) [Fact (2 < L)] (a : (ons_decGraph L).Dart)
    (x : ZMod (8 * L) × ZMod (8 * L)) :
    x ∈ ons_decDartSegment L a ↔
      x ∈ (ons_decEdgeRoute L a.fst a.snd a.adj).support.tail.dropLast ∨
        x = ons_decEmbedVertex L a.snd := by
  rw [ons_decDartSegment, ons_decEdgeRoute_tail_support]
  simp

theorem ons_decDartSegment_nodup
    (L : ℕ) [Fact (2 < L)] (a : (ons_decGraph L).Dart) :
    (ons_decDartSegment L a).Nodup := by
  exact (ons_decEdgeRoute_isPath L a.fst a.snd a.adj).support_nodup.tail

theorem ons_decDartSegment_disjoint
    (L : ℕ) [Fact (2 < L)]
    (a b : (ons_decGraph L).Dart)
    (hedge : a.edge ≠ b.edge) (hsnd : a.snd ≠ b.snd) :
    List.Disjoint (ons_decDartSegment L a) (ons_decDartSegment L b) := by
  rw [List.disjoint_left]
  intro x hxa hxb
  rw [ons_mem_decDartSegment_iff] at hxa hxb
  rcases hxa with hxa | hxa <;> rcases hxb with hxb | hxb
  · apply hedge
    exact ons_decEdgeRoute_edge_eq_of_interior_mem L
      a.fst a.snd b.fst b.snd a.adj b.adj hxa hxb
  · subst x
    exact ons_decEmbedVertex_not_mem_route_interior
      L b.snd a.fst a.snd a.adj hxa
  · subst x
    exact ons_decEmbedVertex_not_mem_route_interior
      L a.snd b.fst b.snd b.adj hxb
  · apply hsnd
    exact ons_decEmbedVertex_injective L (hxa.symm.trans hxb)


end StatMech.Onsager
