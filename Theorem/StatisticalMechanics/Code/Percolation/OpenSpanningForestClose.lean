/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoundaryPruningClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKSpanningTreeClose.Part2
import Def.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem osf_spanForest_spec {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Maximal (fun H => H ≤ G ∧ H.IsAcyclic) (osf_spanForest G) :=
  (Classical.choose_spec
    (exists_maximal_isAcyclic_of_le_isAcyclic (bot_le (a := G)) isAcyclic_bot)).2


theorem osf_spanForest_acyclic {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (osf_spanForest G).IsAcyclic := (osf_spanForest_spec G).1.2


theorem osf_spanForest_le {V : Type*} [Fintype V] (G : SimpleGraph V) :
    osf_spanForest G ≤ G := (osf_spanForest_spec G).1.1


theorem osf_spanForest_reachable {V : Type*} [Fintype V] (G : SimpleGraph V) {u v : V}
    (h : G.Adj u v) : (osf_spanForest G).Reachable u v := by
  classical
  by_contra hnr
  have hmax := osf_spanForest_spec G
  set T := osf_spanForest G with hT
  set T' := T ⊔ SimpleGraph.fromEdgeSet {s(u, v)} with hT'
  have huv_ne : u ≠ v := G.ne_of_adj h
  have hT'ac : T'.IsAcyclic := IsAcyclic.sup_edge_of_not_reachable hnr (osf_spanForest_acyclic G)
  have hT'le : T' ≤ G := by
    refine sup_le (osf_spanForest_le G) ?_
    intro a b hab
    rw [SimpleGraph.fromEdgeSet_adj] at hab
    obtain ⟨hmem, hne⟩ := hab
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact h.symm
  have hle := hmax.2 ⟨hT'le, hT'ac⟩ le_sup_left
  have hadjT : T.Adj u v := by
    apply hle
    rw [hT']; right; rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨by simp, huv_ne⟩
  exact hnr hadjT.reachable


theorem osf_spanForest_reachable_of {V : Type*} [Fintype V] (G : SimpleGraph V) {u v : V}
    (h : G.Reachable u v) : (osf_spanForest G).Reachable u v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab w ih => exact (osf_spanForest_reachable G hab).trans ih


theorem osf_spanForest_degree_pos_of_reachable_ne {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel (osf_spanForest G).Adj] {u v : V} (hv : v ≠ u)
    (h : G.Reachable u v) : 1 ≤ (osf_spanForest G).degree u := by
  classical
  have hr : (osf_spanForest G).Reachable u v := osf_spanForest_reachable_of G h
  have hex : ∃ w, (osf_spanForest G).Adj u w := by
    obtain ⟨p⟩ := hr
    cases p with
    | nil => exact absurd rfl hv
    | cons hadj _ => exact ⟨_, hadj⟩
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, (osf_spanForest G).degree_pos_iff_exists_adj]
  exact hex


theorem osf_spanForest_of_acyclic {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) : osf_spanForest G = G := by
  have hmax := osf_spanForest_spec G
  have hle : osf_spanForest G ≤ G := (osf_spanForest_spec G).1.1
  have hge : G ≤ osf_spanForest G := hmax.2 ⟨le_refl G, hG⟩ hle
  exact le_antisymm hle hge


theorem osf_spanForest_degree_of_acyclic {V : Type*} [Fintype V] (F₀ : SimpleGraph V)
    (hac : F₀.IsAcyclic) [DecidableRel F₀.Adj] [DecidableRel (osf_spanForest F₀).Adj] (v : V) :
    (osf_spanForest F₀).degree v = F₀.degree v := by
  have heq : osf_spanForest F₀ = F₀ := osf_spanForest_of_acyclic F₀ hac
  have h1 : (osf_spanForest F₀).degree v = ((osf_spanForest F₀).neighborFinset v).card :=
    (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
  have h2 : F₀.degree v = (F₀.neighborFinset v).card :=
    (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
  rw [h1, h2, SimpleGraph.neighborFinset_def, SimpleGraph.neighborFinset_def]
  have hns : (osf_spanForest F₀).neighborSet v = F₀.neighborSet v := by rw [heq]
  rw [Set.toFinset_congr hns]


end Percolation
end StatMech
