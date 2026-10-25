/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part15
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem mem_range_doubledAlignedSlotEmbedding_iff_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (v : T.Vertex) (side : Bool) :
    (v, side) ∈ Set.range
        (doubledAlignedSlotEmbedding homega heta hdegree layer) ↔
      (sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v)).card = 2 := by
  constructor
  · rintro ⟨⟨d, branch⟩, h⟩
    have hv : d.1.1.1 = v := by
      exact congrArg (fun z : T.Vertex × Bool => z.1) h
    rw [← hv]
    exact sixVertexDisagreementDart_local_card_eq_two hdegree d.1
  · intro hactive
    let d := orientedDisagreementDartAtActiveVertex
      homega heta v hactive
    let selected := orientedDartBoundaryAlignedSlot
      homega heta hdegree layer d
    by_cases hs : side = selected
    · refine ⟨(d, false), ?_⟩
      change (doubledAlignedVertex (d, false),
        doubledAlignedSlot homega heta hdegree layer (d, false)) =
        (v, side)
      apply Prod.ext
      · rfl
      · change selected = side
        exact hs.symm
    · have hs' : side = !selected := by
        cases side <;> cases hsel : selected <;> simp_all
      refine ⟨(d, true), ?_⟩
      change (doubledAlignedVertex (d, true),
        doubledAlignedSlot homega heta hdegree layer (d, true)) =
        (v, side)
      apply Prod.ext
      · rfl
      · change Bool.not selected = side
        exact hs'.symm

end ScratchLocalRetieC
