/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part8
open StatMech.FrontierD


namespace StatMech.FrontierD

noncomputable def orientedDisagreementDartAtActiveVertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (v : T.Vertex)
    (hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2) :
    SixVertexOrientedDisagreementDart omega eta := by
  let hex := exists_incoming_disagreement_side
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexLocalIncomingPattern eta v)
    (sixVertexLocalIncomingPattern_ice omega homega v)
    (sixVertexLocalIncomingPattern_ice eta heta v) hactive
  let side := Classical.choose hex
  let hs := Classical.choose_spec hex
  let dart : SixVertexDisagreementDart omega eta :=
    ⟨(v, side), by
      change sixVertexTorusEdgeDisagrees omega eta
        (sixVertexTorusIncidentEdge T v side)
      rw [← sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
      exact bne_iff_ne.mp hs.1⟩
  exact ⟨dart, hs.2⟩

end StatMech.FrontierD
