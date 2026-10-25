/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.SpinCharacter.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13
import Def.StatisticalMechanics.Code.Onsager.DecorationSum.Part2


namespace StatMech.Onsager

open BigOperators StatMech.Ising

@[simp] theorem ons_decEdgeProjection_external (L : ℕ) (d : ons_Dart L) :
    ons_decEdgeProjection s(d, ons_dartRev L d) = ons_portEdge L d :=
  rfl

theorem ons_decEdgeProjection_injective_of_external
    (L : ℕ) [Fact (2 < L)]
    {edge edge' : Sym2 (ons_Dart L)}
    (he : ons_decIsExternal edge) (he' : ons_decIsExternal edge')
    (hproj : ons_decEdgeProjection edge = ons_decEdgeProjection edge') :
    edge = edge' := by
  rcases he with ⟨d, rfl⟩
  rcases he' with ⟨e, rfl⟩
  simp only [ons_decEdgeProjection_external] at hproj
  rcases (ons_portEdge_eq_iff L e d).mp hproj with h | h
  · subst d
    rfl
  · subst d
    rw [ons_dartRev_involutive]
    exact Sym2.eq_swap


theorem ons_decoratedExternalEdges_image
    (L : ℕ) [Fact (2 < L)]
    (D : ons_DecoratedEvenSubgraph L) :
    (ons_decoratedExternalEdges D.1).image ons_decEdgeProjection =
      ons_originalEdgesOfDecorated L D := by
  classical
  rw [ons_originalEdgesOfDecorated_eq_portPatternEdges]
  ext edge
  constructor
  · rw [Finset.mem_image]
    rintro ⟨edge', hedge', hproj⟩
    rw [ons_decoratedExternalEdges, Finset.mem_filter] at hedge'
    rcases hedge'.2 with ⟨d, rfl⟩
    rw [ons_decEdgeProjection_external] at hproj
    subst edge
    rw [ons_portEdge_mem_portPatternEdges_iff]
    change ons_decoratedPortBit D.1 d = 1
    simp [ons_decoratedPortBit, hedge'.1]
  · intro hedge
    rw [ons_portPatternEdges, Finset.mem_image] at hedge
    rcases hedge with ⟨d, hd, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    have hdD : s(d, ons_dartRev L d) ∈ D.1 := by
      change (if s(d, ons_dartRev L d) ∈ D.1 then (1 : Fin 2) else 0) = 1 at hd
      simpa using hd
    rw [Finset.mem_image]
    refine ⟨s(d, ons_dartRev L d), ?_, ons_decEdgeProjection_external L d⟩
    rw [ons_decoratedExternalEdges, Finset.mem_filter]
    exact ⟨hdD, ⟨d, rfl⟩⟩


theorem ons_originalEdgesOfDecorated_card
    (L : ℕ) [Fact (2 < L)]
    (D : ons_DecoratedEvenSubgraph L) :
    (ons_originalEdgesOfDecorated L D).card =
      (ons_decoratedExternalEdges D.1).card := by
  classical
  rw [← ons_decoratedExternalEdges_image L D]
  apply Finset.card_image_of_injOn
  intro edge hedge edge' hedge' hproj
  have hext := (Finset.mem_filter.mp (Finset.mem_coe.mp hedge)).2
  have hext' := (Finset.mem_filter.mp (Finset.mem_coe.mp hedge')).2
  exact ons_decEdgeProjection_injective_of_external L hext hext' hproj

end StatMech.Onsager
