/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorGapDefects_transport_of_forward_disjoint
    {N n : Nat} (x y : SixVertexSector N n)
    (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y))
    (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)))
    (i : Fin n) :
    sixVertexSectorGapDefects y i +
        sixVertexSectorAdvanceDefects x y i =
      sixVertexSectorGapDefects x i +
        sixVertexSectorAdvanceDefects x y (sixVertexSectorCyclicNext i) := by
  have hsupport := sixVertexSectorNoAdjacent_pair_of_forward_disjoint
    x y hforward hdisj
  have htransport := sixVertexSectorGap_transport_of_forward_disjoint
    x y hforward hdisj i
  have hgapx := sixVertexSectorGap_pos_of_noAdjacent x hsupport.1 i
  have hgapy := sixVertexSectorGap_pos_of_noAdjacent y hsupport.2 i
  have hadvi := sixVertexSectorAdvance_pos_of_forward_disjoint
    x y hforward hdisj i
  have hadvn := sixVertexSectorAdvance_pos_of_forward_disjoint
    x y hforward hdisj (sixVertexSectorCyclicNext i)
  rw [sixVertexSectorGapDefects, sixVertexSectorGapDefects,
    sixVertexSectorAdvanceDefects, sixVertexSectorAdvanceDefects]
  omega

theorem sixVertexSectorAdvanceDefects_le_gapDefects_of_forward_disjoint
    {N n : Nat} (x y : SixVertexSector N n)
    (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y))
    (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)))
    (i : Fin n) :
    sixVertexSectorAdvanceDefects x y i ≤
      sixVertexSectorGapDefects x i := by
  have hpos := sixVertexSectorAdvance_pos_of_forward_disjoint
    x y hforward hdisj i
  have hle := sixVertexSectorAdvance_le_gap_of_forward_disjoint
    x y hforward hdisj i
  rw [sixVertexSectorAdvanceDefects, sixVertexSectorGapDefects]
  omega

theorem sixVertexInfinityGraph_adj_iff_forward_disjoint
    {N n : Nat} (hn : 0 < n) (x y : SixVertexSector N n) :
    (sixVertexInfinityGraph N n).Adj x y ↔
      (SixVertexForwardInterlaced (sixVertexSectorRow x)
          (sixVertexSectorRow y) ∧
        Disjoint (x : Finset (Fin N)) (y : Finset (Fin N))) ∨
      (SixVertexForwardInterlaced (sixVertexSectorRow y)
          (sixVertexSectorRow x) ∧
        Disjoint (x : Finset (Fin N)) (y : Finset (Fin N))) := by
  change (x ≠ y ∧
      SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) ∧
      sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) =
        2 * n) ↔ _
  rw [sixVertexSectorRowDistance_eq_twice_iff_disjoint]
  constructor
  · rintro ⟨_, hforward | hbackward, hdisj⟩
    · exact Or.inl ⟨hforward, hdisj⟩
    · exact Or.inr ⟨hbackward, hdisj⟩
  · rintro (⟨hforward, hdisj⟩ | ⟨hbackward, hdisj⟩)
    · refine ⟨?_, Or.inl hforward, hdisj⟩
      intro hxy
      subst y
      have hcard : (x : Finset (Fin N)).card = n := x.prop
      have : (x : Finset (Fin N)) = ∅ := disjoint_self.mp hdisj
      rw [this] at hcard
      simp at hcard
      omega
    · refine ⟨?_, Or.inr hbackward, hdisj⟩
      intro hxy
      subst y
      have hcard : (x : Finset (Fin N)).card = n := x.prop
      have : (x : Finset (Fin N)) = ∅ := disjoint_self.mp hdisj
      rw [this] at hcard
      simp at hcard
      omega

theorem sixVertexInfinityGraph_adj_defect_transport
    {N n : Nat} (hn : 0 < n) {x y : SixVertexSector N n}
    (hxy : (sixVertexInfinityGraph N n).Adj x y) :
    (∀ i,
      sixVertexSectorGapDefects y i +
          sixVertexSectorAdvanceDefects x y i =
        sixVertexSectorGapDefects x i +
          sixVertexSectorAdvanceDefects x y (sixVertexSectorCyclicNext i)) ∨
    (∀ i,
      sixVertexSectorGapDefects x i +
          sixVertexSectorAdvanceDefects y x i =
        sixVertexSectorGapDefects y i +
          sixVertexSectorAdvanceDefects y x (sixVertexSectorCyclicNext i)) := by
  rcases (sixVertexInfinityGraph_adj_iff_forward_disjoint hn x y).mp hxy with
      ⟨hforward, hdisj⟩ | ⟨hbackward, hdisj⟩
  · exact Or.inl (sixVertexSectorGapDefects_transport_of_forward_disjoint
      x y hforward hdisj)
  · exact Or.inr (sixVertexSectorGapDefects_transport_of_forward_disjoint
      y x hbackward hdisj.symm)

theorem sixVertexInfinityGraph_adj_iff (N n : Nat)
    (x y : SixVertexSector N n) :
    (sixVertexInfinityGraph N n).Adj x y ↔
      x ≠ y ∧ SixVertexInterlaced (sixVertexSectorRow x)
        (sixVertexSectorRow y) ∧
        sixVertexRowDistance (sixVertexSectorRow x)
          (sixVertexSectorRow y) = 2 * n :=
  Iff.rfl

theorem sixVertexInfinityGraph_adjMatrix :
    (sixVertexInfinityGraph N n).adjMatrix Real =
      sixVertexSectorTransferInfinity N n := by
  classical
  ext x y
  simp [SimpleGraph.adjMatrix, sixVertexInfinityGraph,
    sixVertexSectorTransferInfinity]


theorem sixVertexSectorTransferInfinity_pow_apply_eq_card_walk
    (M N n : Nat) (x y : SixVertexSector N n) :
    (sixVertexSectorTransferInfinity N n ^ M) x y =
      Fintype.card {w : (sixVertexInfinityGraph N n).Walk x y |
        w.length = M} := by
  classical
  rw [← sixVertexInfinityGraph_adjMatrix]
  exact SimpleGraph.adjMatrix_pow_apply_eq_card_walk M x y


theorem trace_sixVertexSectorTransferInfinity_pow_eq_closedWalks
    (M N n : Nat) :
    Matrix.trace (sixVertexSectorTransferInfinity N n ^ M) =
      ∑ x : SixVertexSector N n,
        (Fintype.card {w : (sixVertexInfinityGraph N n).Walk x x |
          w.length = M} : Real) := by
  classical
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro x hx
  exact sixVertexSectorTransferInfinity_pow_apply_eq_card_walk M N n x x


theorem AnalyticOnNhd.eqOn_Ioi_of_eventuallyEq_atTop
    {f g : Real → Real} {a : Real}
    (hf : AnalyticOnNhd Real f (Set.Ioi a))
    (hg : AnalyticOnNhd Real g (Set.Ioi a))
    (hfg : f =ᶠ[atTop] g) : Set.EqOn f g (Set.Ioi a) := by
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp hfg
  let z0 := max (a + 1) (b + 1)
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_Ioi
      (z₀ := z0)
  · change a < z0
    dsimp [z0]
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · filter_upwards [Ioi_mem_nhds (show b < z0 by
      dsimp [z0]
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _))] with z hz
    exact hb z hz.le

end
end StatMech.FrontierD
