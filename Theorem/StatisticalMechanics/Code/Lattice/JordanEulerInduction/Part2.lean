/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleRank.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanEulerInduction
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem jei_pushGraph_adj (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (a b : Site 2) :
    (jei_pushGraph P K).Adj a b ↔ ∃ x y : P.V, K.Adj x y ∧ P.emb x = a ∧ P.emb y = b := Iff.rfl


theorem jei_pushGraph_G (P : PlanarZ2Subgraph) : jei_pushGraph P P.G = imageGraph P := by
  ext a b; rw [jei_pushGraph_adj, imageGraph_adj]


theorem jei_pushGraph_bot (P : PlanarZ2Subgraph) : jei_pushGraph P ⊥ = ⊥ := by
  ext a b; rw [jei_pushGraph_adj]
  simp only [SimpleGraph.bot_adj, iff_false]
  rintro ⟨x, y, hadj, _, _⟩; exact hadj.elim


theorem jei_pushGraph_edgeSet_finite (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    (jei_pushGraph P K).edgeSet.Finite := by
  have hV : Finite P.V := P.finV
  apply Set.Finite.subset (Set.finite_range (Sym2.map P.emb : Sym2 P.V → Sym2 (Site 2)))
  intro e he
  induction e with
  | _ a b =>
    rw [SimpleGraph.mem_edgeSet, jei_pushGraph_adj] at he
    obtain ⟨x, y, hK, rfl, rfl⟩ := he
    exact ⟨s(x, y), by simp⟩


theorem jei_pushGraph_regionComponents_finite (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    Finite (regionGraph (jei_pushGraph P K)).ConnectedComponent :=
  jei_regionComponents_finite _ (jei_pushGraph_edgeSet_finite P K)


theorem jei_pushGraph_sup_edge (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (x y : P.V)
    (hne : x ≠ y) :
    jei_pushGraph P (K ⊔ edge x y) = jei_pushGraph P K ⊔ edge (P.emb x) (P.emb y) := by
  ext a b
  simp only [jei_pushGraph_adj, sup_adj, edge_adj]
  constructor
  · rintro ⟨u, v, huv, rfl, rfl⟩
    rcases huv with hK | ⟨hxy, _⟩
    · exact Or.inl ⟨u, v, hK, rfl, rfl⟩
    · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, fun h => hne (P.emb.injective h)⟩
      · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, fun h => hne (P.emb.injective h).symm⟩
  · rintro (⟨u, v, hK, rfl, rfl⟩ | ⟨hab, hne'⟩)
    · exact ⟨u, v, Or.inl hK, rfl, rfl⟩
    · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨x, y, Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩, rfl, rfl⟩
      · exact ⟨y, x, Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hne.symm⟩, rfl, rfl⟩


theorem jei_push_reachable_iff (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (x y : P.V) :
    (jei_pushGraph P K).Reachable (P.emb x) (P.emb y) ↔ K.Reachable x y := by
  constructor
  · rintro ⟨w⟩
    suffices h : ∀ (a b : Site 2) (w : (jei_pushGraph P K).Walk a b) (za zb : P.V),
        P.emb za = a → P.emb zb = b → K.Reachable za zb by
      exact h _ _ w x y rfl rfl
    intro a b w
    induction w with
    | nil =>
      intro za zb hza hzb
      have : za = zb := P.emb.injective (hza.trans hzb.symm)
      subst this; exact Reachable.refl za
    | @cons c d e hcd wde ih =>
      intro za zb hza hzb
      obtain ⟨u, v, hKuv, hu, hv⟩ := hcd
      have hzau : za = u := P.emb.injective (hza.trans hu.symm)
      subst hzau
      exact (hKuv.reachable).trans (ih v zb hv hzb)
  · intro h
    refine h.map (⟨P.emb, ?_⟩ : K →g jei_pushGraph P K)
    intro a b hab; exact ⟨a, b, hab, rfl, rfl⟩


theorem jei_crossEdge_present (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) {x y : P.V}
    (hadjG : P.G.Adj x y) (hnotK : ¬ K.Adj x y) :
    crossEdge s(P.emb x, P.emb y) ∈ (regionGraph (jei_pushGraph P K)).edgeSet := by
  rw [crossEdge_mk, SimpleGraph.mem_edgeSet, regionGraph_adj]
  refine ⟨(rot90_adj _ _).mpr (P.isSub hadjG), ?_⟩
  rw [← crossEdge_mk, Equiv.symm_apply_apply, SimpleGraph.mem_edgeSet, jei_pushGraph_adj]
  rintro ⟨u, v, hKuv, hu, hv⟩
  have hux : u = x := P.emb.injective hu
  have hvy : v = y := P.emb.injective hv
  subst_vars
  exact hnotK hKuv


end Lattice
end StatMech
