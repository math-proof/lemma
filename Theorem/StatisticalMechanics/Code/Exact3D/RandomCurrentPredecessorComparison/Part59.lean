/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Structure.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part9
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem simpleGraphIso_edist_eq
    {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
    (ψ : G ≃g G') (u v : V) :
    G'.edist (ψ u) (ψ v) = G.edist u v := by
  by_cases hreach : G.Reachable u v
  · have hreach' : G'.Reachable (ψ u) (ψ v) := hreach.map ψ.toHom
    obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_edist
    obtain ⟨q, hq⟩ := hreach'.exists_walk_length_eq_edist
    apply le_antisymm
    · calc
        G'.edist (ψ u) (ψ v) ≤ (p.map ψ.toHom).length :=
          SimpleGraph.edist_le _
        _ = p.length := by rw [SimpleGraph.Walk.length_map]
        _ = G.edist u v := hp
    · calc
        G.edist u v ≤ (q.map ψ.symm.toHom).length := by
          simpa using
            (SimpleGraph.edist_le (p := q.map ψ.symm.toHom))
        _ = q.length := by rw [SimpleGraph.Walk.length_map]
        _ = G'.edist (ψ u) (ψ v) := hq
  · have hreach' : ¬ G'.Reachable (ψ u) (ψ v) := by
      intro h'
      exact hreach
        ((SimpleGraph.Iso.reachable_iff (φ := ψ) (u := u) (v := v)).mp h')
    rw [SimpleGraph.edist_eq_top_of_not_reachable hreach',
      SimpleGraph.edist_eq_top_of_not_reachable hreach]

set_option linter.style.longLine false in


theorem doubledBoxCompatibleEdgeRelabel_adj_iff
    {n : ℕ}
    (φ : FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (σ :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hends : ∀ e, (σ e).1 = Sym2.map φ e.1)
    (a b : FK.boxVerts 3 (2 * n)) :
    (FK.boxGraph 3 (2 * n)).Adj (φ a) (φ b) ↔
      (FK.boxGraph 3 (2 * n)).Adj a b := by
  constructor
  · intro hab
    let eφ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset :=
      ⟨s(φ a, φ b), by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact hab⟩
    let e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset := σ.symm eφ
    have hσe : σ e = eφ := by
      simp [e, eφ]
    have hmap : Sym2.map φ e.1 = Sym2.map φ s(a, b) := by
      calc
        Sym2.map φ e.1 = (σ e).1 := (hends e).symm
        _ = eφ.1 := by rw [hσe]
        _ = s(φ a, φ b) := rfl
        _ = Sym2.map φ s(a, b) := by rw [Sym2.map_mk]
    have heq : e.1 = s(a, b) :=
      (Sym2.map.injective φ.injective) hmap
    have hmem : s(a, b) ∈ (FK.boxGraph 3 (2 * n)).edgeFinset := by
      rw [← heq]
      exact e.2
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hmem
    exact hmem
  · intro hab
    let e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset :=
      ⟨s(a, b), by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact hab⟩
    have hmem :
        Sym2.map φ s(a, b) ∈
          (FK.boxGraph 3 (2 * n)).edgeFinset := by
      rw [← hends e]
      exact (σ e).2
    rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet] at hmem
    exact hmem

end Exact3D
end StatMech
