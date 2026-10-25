/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorCentralFace_mem_region {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hn : 0 < n) :
    rlc_connectorCentralFace ∈
      rlc_connectorCentralFaceRegion gamma gamma' := by
  have hs := rlc_connectorCentralFace_mem_faceBox hn
  have hset : rlc_connectorCentralFace ∈
      rlc_connectorCentralFaceRegionSet gamma gamma' :=
    ⟨hs, hs, ⟨SimpleGraph.Walk.nil⟩⟩
  simpa [rlc_connectorCentralFaceRegion] using hset


theorem rlc_connectorCentralFaceRegion_of_cut_adj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {f g : Site 2}
    (hf : f ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hgBox : g ∈ rlc_connectorFaceBox n)
    (hfg : (rlc_connectorFourTraceFaceCutGraph gamma gamma').Adj f g) :
    g ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  have hfSet : f ∈ rlc_connectorCentralFaceRegionSet gamma gamma' := by
    simpa [rlc_connectorCentralFaceRegion] using hf
  obtain ⟨hfBox, hs, hreach⟩ := hfSet
  have hstep : (rlc_connectorFiniteFaceCutGraph gamma gamma').Adj
      ⟨f, hfBox⟩ ⟨g, hgBox⟩ := hfg
  have hgSet : g ∈ rlc_connectorCentralFaceRegionSet gamma gamma' :=
    ⟨hgBox, hs, hreach.trans hstep.reachable⟩
  simpa [rlc_connectorCentralFaceRegion] using hgSet

theorem rlc_connectorCentralFaceRegion_of_cut_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {f g : Site 2}
    (hf : f ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hfBox : f ∈ rlc_connectorFaceBox n)
    (hgBox : g ∈ rlc_connectorFaceBox n)
    (hfg : (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
      ⟨f, hfBox⟩ ⟨g, hgBox⟩) :
    g ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  have hfSet : f ∈ rlc_connectorCentralFaceRegionSet gamma gamma' := by
    simpa [rlc_connectorCentralFaceRegion] using hf
  obtain ⟨_hfBox, hs, hcentral⟩ := hfSet
  have hfEq : (⟨f, hfBox⟩ : RlcConnectorFaceVertex n) = ⟨f, _hfBox⟩ := rfl
  rw [hfEq] at hfg
  have hgSet : g ∈ rlc_connectorCentralFaceRegionSet gamma gamma' :=
    ⟨hgBox, hs, hcentral.trans hfg⟩
  simpa [rlc_connectorCentralFaceRegion] using hgSet


end
end StatMech.Universality
