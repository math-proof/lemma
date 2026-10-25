/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part3
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem finiteBoundaryEdgeRun_adj_iff
    {V B : Type*} (embed : B -> V) (G : SimpleGraph V)
    (edges : List (B × B)) (u v : V) :
    (finiteBoundaryEdgeRun embed G edges).Adj u v ↔
      G.Adj u v ∨ ∃ e ∈ edges,
        (SimpleGraph.edge (embed e.1) (embed e.2)).Adj u v := by
  induction edges generalizing G with
  | nil => simp [finiteBoundaryEdgeRun]
  | cons e edges ih =>
      rw [finiteBoundaryEdgeRun, ih]
      simp only [SimpleGraph.sup_adj, List.mem_cons]
      aesop

theorem finiteBoundaryEdgeRun_reachable_iff
    {V B : Type*} (embed : B -> V) (G : SimpleGraph V) (K : SimpleGraph B)
    (hreach : ∀ x y, G.Reachable (embed x) (embed y) ↔ K.Reachable x y)
    (edges : List (B × B)) (x y : B) :
    (finiteBoundaryEdgeRun embed G edges).Reachable (embed x) (embed y) ↔
      (finiteBoundaryEdgeRun id K edges).Reachable x y := by
  induction edges generalizing G K with
  | nil => exact hreach x y
  | cons e edges ih =>
      apply ih
      intro u v
      rw [StatMech.Lattice.reachable_sup_edge,
        StatMech.Lattice.reachable_sup_edge]
      simp only [hreach, id_eq]


theorem finiteBoundaryEdgeRun_component_cross_sum
    {V B : Type*} [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]
    (embed : B -> V) (G : SimpleGraph V) (K : SimpleGraph B)
    (hreach : ∀ x y, G.Reachable (embed x) (embed y) ↔ K.Reachable x y)
    (edges : List (B × B)) :
    Nat.card G.ConnectedComponent +
        Nat.card (finiteBoundaryEdgeRun id K edges).ConnectedComponent =
      Nat.card K.ConnectedComponent +
        Nat.card (finiteBoundaryEdgeRun embed G edges).ConnectedComponent := by
  induction edges generalizing G K with
  | nil => simp [finiteBoundaryEdgeRun, Nat.add_comm]
  | cons e edges ih =>
      let G' := G ⊔ SimpleGraph.edge (embed e.1) (embed e.2)
      let K' := K ⊔ SimpleGraph.edge e.1 e.2
      have hreach' : ∀ x y,
          G'.Reachable (embed x) (embed y) ↔ K'.Reachable x y := by
        intro x y
        dsimp only [G', K']
        rw [StatMech.Lattice.reachable_sup_edge,
          StatMech.Lattice.reachable_sup_edge]
        simp only [hreach, id_eq]
      have hind := ih G' K' hreach'
      simp only [finiteBoundaryEdgeRun] at hind ⊢
      by_cases hk : K.Reachable e.1 e.2
      · have hg : G.Reachable (embed e.1) (embed e.2) :=
          (hreach e.1 e.2).2 hk
        have hG := StatMech.Lattice.card_components_sup_edge_of_reachable
          G (embed e.1) (embed e.2) hg
        have hK := StatMech.Lattice.card_components_sup_edge_of_reachable
          K e.1 e.2 hk
        dsimp only [G', K'] at hind
        simp only [id_eq] at hind
        rw [hG, hK] at hind
        exact hind
      · have hg : ¬G.Reachable (embed e.1) (embed e.2) := by
          exact fun h => hk ((hreach e.1 e.2).1 h)
        have hG := StatMech.Lattice.card_components_sup_edge_of_not_reachable
          G (embed e.1) (embed e.2) hg
        have hK := StatMech.Lattice.card_components_sup_edge_of_not_reachable
          K e.1 e.2 hk
        dsimp only [G', K'] at hind
        calc
          Nat.card G.ConnectedComponent +
                Nat.card (finiteBoundaryEdgeRun id K (e :: edges)).ConnectedComponent =
              (Nat.card (G ⊔ SimpleGraph.edge (embed e.1) (embed e.2)).ConnectedComponent + 1) +
                Nat.card (finiteBoundaryEdgeRun id K (e :: edges)).ConnectedComponent := by
                  rw [hG]
          _ = (Nat.card (G ⊔ SimpleGraph.edge (embed e.1) (embed e.2)).ConnectedComponent +
                Nat.card (finiteBoundaryEdgeRun id
                  (K ⊔ SimpleGraph.edge e.1 e.2) edges).ConnectedComponent) + 1 := by
                  simp only [finiteBoundaryEdgeRun, id_eq]
                  ac_rfl
          _ = (Nat.card (K ⊔ SimpleGraph.edge e.1 e.2).ConnectedComponent +
                Nat.card (finiteBoundaryEdgeRun embed
                  (G ⊔ SimpleGraph.edge (embed e.1) (embed e.2)) edges).ConnectedComponent) + 1 := by
                  rw [hind]
          _ = Nat.card K.ConnectedComponent +
                Nat.card (finiteBoundaryEdgeRun embed G (e :: edges)).ConnectedComponent := by
                  simp only [finiteBoundaryEdgeRun]
                  omega


end
end StatMech.FrontierD
