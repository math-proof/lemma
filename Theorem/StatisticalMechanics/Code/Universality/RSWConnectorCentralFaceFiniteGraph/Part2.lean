/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceDualFrame.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFiniteGraph.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_exists_connector_iff_traceAnchors {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n)) :
    (∃ x y : RlcConnectorVertex n,
        rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
          H.Reachable x y) ↔
      (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable
        (rlc_connectorRightAnchor gamma)
        (rlc_connectorLeftAnchor gamma') := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hright := (rlc_connectorTraceWiring_reachable_right gamma gamma'
      (rlc_connectorRightAnchor_onRight gamma) hx).mono
        (show rlc_connectorTraceWiring gamma gamma' ≤
          H ⊔ rlc_connectorTraceWiring gamma gamma' from le_sup_right)
    have hmiddle : (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable x y :=
      hxy.mono le_sup_left
    have hleft := (rlc_connectorTraceWiring_reachable_left gamma gamma'
      hy (rlc_connectorLeftAnchor_onLeft gamma')).mono
        (show rlc_connectorTraceWiring gamma gamma' ≤
          H ⊔ rlc_connectorTraceWiring gamma gamma' from le_sup_right)
    exact hright.trans (hmiddle.trans hleft)
  · intro hanchors
    by_contra hno
    have hpropagate : ∀ {u v : RlcConnectorVertex n},
        (H ⊔ rlc_connectorSeparateWiring gamma gamma').Walk u v →
        (∃ x, rlc_connectorOnRight gamma x ∧ H.Reachable x u) →
        ∃ x, rlc_connectorOnRight gamma x ∧ H.Reachable x v := by
      intro u v w
      induction w with
      | nil => exact fun hu => hu
      | @cons u v z huv w ih =>
          intro hu
          apply ih
          rcases huv with hH | hsep
          · obtain ⟨x, hx, hxu⟩ := hu
            exact ⟨x, hx, hxu.trans hH.reachable⟩
          · rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj] at hsep
            rcases hsep with hright | hleft
            · rw [Lattice.boundaryCliqueGraph_adj] at hright
              exact ⟨v, hright.2.2, Reachable.refl _⟩
            · rw [Lattice.boundaryCliqueGraph_adj] at hleft
              obtain ⟨x, hx, hxu⟩ := hu
              exact False.elim (hno ⟨x, u, hx, hleft.2.1, hxu⟩)
    have hanchorsSeparate :
        (H ⊔ rlc_connectorSeparateWiring gamma gamma').Reachable
          (rlc_connectorRightAnchor gamma)
          (rlc_connectorLeftAnchor gamma') :=
      (rlc_connectorTraceWiring_reachable_iff_separateWiring gamma gamma' H
        (rlc_connectorRightAnchor gamma)
        (rlc_connectorLeftAnchor gamma')).mp hanchors
    obtain ⟨w⟩ := hanchorsSeparate
    obtain ⟨x, hx, hxleft⟩ := hpropagate w
      ⟨rlc_connectorRightAnchor gamma,
        rlc_connectorRightAnchor_onRight gamma, Reachable.refl _⟩
    exact hno ⟨x, rlc_connectorLeftAnchor gamma', hx,
      rlc_connectorLeftAnchor_onLeft gamma', hxleft⟩

theorem centralFaceEdge_exists_lift {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma') :
    ∃ f : Sym2 (RlcConnectorVertex n), f.map Subtype.val = e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hx := rlc_connectorCentralFaceEdge_endpoints_mem_box
        gamma gamma' he (Sym2.mem_mk_left x y)
      have hy := rlc_connectorCentralFaceEdge_endpoints_mem_box
        gamma gamma' he (Sym2.mem_mk_right x y)
      exact ⟨s(⟨x, by simpa [rlc_connectorBox] using hx⟩,
          ⟨y, by simpa [rlc_connectorBox] using hy⟩), by
        simp [Sym2.map_mk]⟩

end
end StatMech.Universality
