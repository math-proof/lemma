/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

noncomputable def sixVertexDegreeTwoBranchPredecessor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (branch : Bool)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    SixVertexOrientedDisagreementDart omega eta :=
  ((doubledAlignedFirstReturnPerm homega heta hdegree).symm (d, branch)).1


noncomputable def sixVertexDegreeTwoSynchronizedGraph
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    SimpleGraph (SixVertexOrientedDisagreementDart omega eta) where
  Adj a b := a ≠ b ∧ ∃ d,
    (a = sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d ∧
      b = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d) ∨
    (b = sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d ∧
      a = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d)
  symm := by
    constructor
    rintro a b ⟨hne, d, h | h⟩
    · exact ⟨hne.symm, d, Or.inr ⟨h.1, h.2⟩⟩
    · exact ⟨hne.symm, d, Or.inl ⟨h.1, h.2⟩⟩
  loopless := by
    exact ⟨fun a h => h.1 rfl⟩

end
end StatMech.FrontierD
