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
import Theorem.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part12
open StatMech.FrontierD


namespace ScratchLocalRetieC

noncomputable def doubledAlignedSlotEmbedding
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) :
    DoubledAlignedState omega eta ↪ T.Vertex × Bool where
  toFun x := (doubledAlignedVertex x,
    doubledAlignedSlot homega heta hdegree layer x)
  inj' := by
    intro x y hxy
    change (doubledAlignedVertex x,
      doubledAlignedSlot homega heta hdegree layer x) =
      (doubledAlignedVertex y,
        doubledAlignedSlot homega heta hdegree layer y) at hxy
    have hv : doubledAlignedVertex x = doubledAlignedVertex y :=
      congrArg (fun z : T.Vertex × Bool => z.1) hxy
    have hd : x.1 = y.1 := orientedDisagreementDart_eq_of_vertex_eq
      homega heta hdegree x.1 y.1 hv
    rcases x with ⟨d, branchX⟩
    rcases y with ⟨e, branchY⟩
    simp only at hd
    subst e
    apply Prod.ext
    · rfl
    · have hs := congrArg (fun z : T.Vertex × Bool => z.2) hxy
      change (if branchX then
          !orientedDartBoundaryAlignedSlot homega heta hdegree layer d
        else orientedDartBoundaryAlignedSlot homega heta hdegree layer d) =
        (if branchY then
          !orientedDartBoundaryAlignedSlot homega heta hdegree layer d
        else orientedDartBoundaryAlignedSlot homega heta hdegree layer d) at hs
      cases branchX <;> cases branchY <;> simp_all

end ScratchLocalRetieC
