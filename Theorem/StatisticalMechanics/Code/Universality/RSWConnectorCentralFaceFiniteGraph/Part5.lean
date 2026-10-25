/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceDualFrame.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFiniteGraph.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorCentralFacePIMSConfig_apply {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n)) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho e =
      !(rlc_connectorCentralFaceAmbientConfig gamma gamma' rho
        (rlc_pimsEdgeEquiv (e.map Subtype.val))) := by
  unfold rlc_connectorCentralFacePIMSConfig rlc_connectorRestrictConfig
  exact rlc_dualReflectConfig_eq_pims _ _

theorem centralFaceEdgeLift_eq_mk {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {x y : RlcConnectorVertex n}
    (he : s((x : Site 2), (y : Site 2)) ∈
      rlc_connectorCentralFaceEdges gamma gamma') :
    rlc_connectorCentralFaceEdgeLift
        s((x : Site 2), (y : Site 2)) he = s(x, y) := by
  apply Sym2.map.injective Subtype.val_injective
  rw [rlc_connectorCentralFaceEdgeLift_map]
  rfl


theorem rlc_openSub_centralFaceClosure_ambient {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma')
        (rlc_connectorRestrictConfig
          (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)) =
      FK.openSub (rlc_connectorCentralFaceFiniteGraph gamma gamma') rho ⊔
        rlc_connectorTraceWiring gamma gamma' := by
  ext x y
  rw [FK.openSub_adj, SimpleGraph.sup_adj]
  let e : Sym2 (Site 2) := s((x : Site 2), (y : Site 2))
  have herase : (s(x, y) : Sym2 (RlcConnectorVertex n)).map Subtype.val = e := by
    rfl
  constructor
  · rintro ⟨⟨hxy, hplanar⟩, hopen⟩
    change rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = true at hopen
    by_cases hrandom : e ∈ rlc_connectorCentralFaceEdges gamma gamma'
    · left
      refine ⟨⟨hxy, hrandom⟩, ?_⟩
      rw [rlc_connectorCentralFaceAmbientConfig_support
        gamma gamma' rho hrandom, centralFaceEdgeLift_eq_mk hrandom] at hopen
      exact hopen
    · have hfour : e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
        rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union] at hplanar
        rcases hplanar with hclosure | hfour
        · by_contra hnot
          exact hrandom (Finset.mem_sdiff.mpr ⟨hclosure, hnot⟩)
        · exact hfour
      rw [rlc_connectorFourTraceEdges, Finset.mem_union] at hfour
      rcases hfour with horiginal | hreflected
      · right
        exact ⟨hxy, horiginal⟩
      · by_cases horiginal : e ∈
            rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
        · right
          exact ⟨hxy, horiginal⟩
        · simp [rlc_connectorCentralFaceAmbientConfig, hrandom,
            horiginal] at hopen
  · rintro (hrandom | htrace)
    · obtain ⟨⟨hxy, he⟩, hopen⟩ := hrandom
      refine ⟨⟨hxy, ?_⟩, ?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp he).1
      · change rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = true
        rw [rlc_connectorCentralFaceAmbientConfig_support gamma gamma' rho he,
          centralFaceEdgeLift_eq_mk he]
        exact hopen
    · obtain ⟨hxy, he⟩ := htrace
      refine ⟨⟨hxy, ?_⟩, ?_⟩
      · apply Finset.mem_union_right
        rw [rlc_connectorFourTraceEdges, Finset.mem_union]
        exact Or.inl he
      · change rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = true
        exact rlc_connectorCentralFaceAmbientConfig_trace gamma gamma' rho he


theorem rlc_mem_randomConnectorEvent_iff_ambientClosureConnectorEvent
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rho ∈ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma' ↔
      rlc_connectorRestrictConfig
          (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho) ∈
        rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  change
    (∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
        (FK.openSub (rlc_connectorCentralFaceFiniteGraph gamma gamma') rho).Reachable x y) ↔
    (∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
        (FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma')
          (rlc_connectorRestrictConfig
            (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho))).Reachable x y)
  rw [rlc_exists_connector_iff_traceAnchors]
  constructor
  · intro hanchors
    refine ⟨rlc_connectorRightAnchor gamma,
      rlc_connectorLeftAnchor gamma',
      rlc_connectorRightAnchor_onRight gamma,
      rlc_connectorLeftAnchor_onLeft gamma', ?_⟩
    rw [rlc_openSub_centralFaceClosure_ambient]
    exact hanchors
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hright := (rlc_connectorTraceWiring_reachable_right gamma gamma'
      (rlc_connectorRightAnchor_onRight gamma) hx).mono
        (show rlc_connectorTraceWiring gamma gamma' ≤
          FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma')
            (rlc_connectorRestrictConfig
              (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)) by
          rw [rlc_openSub_centralFaceClosure_ambient]
          exact le_sup_right)
    have hleft := (rlc_connectorTraceWiring_reachable_left gamma gamma'
      hy (rlc_connectorLeftAnchor_onLeft gamma')).mono
        (show rlc_connectorTraceWiring gamma gamma' ≤
          FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma')
            (rlc_connectorRestrictConfig
              (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)) by
          rw [rlc_openSub_centralFaceClosure_ambient]
          exact le_sup_right)
    rw [rlc_openSub_centralFaceClosure_ambient] at hright hxy hleft
    exact hright.trans (hxy.trans hleft)

end
end StatMech.Universality
