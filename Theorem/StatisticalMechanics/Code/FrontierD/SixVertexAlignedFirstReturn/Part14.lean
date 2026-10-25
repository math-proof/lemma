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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part16
open StatMech.FrontierD


namespace StatMech.FrontierD

@[simp] theorem doubledAlignedVertex_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (x : DoubledAlignedState omega eta) :
    doubledAlignedVertex (doubledAlignedBranchSwap x) =
      doubledAlignedVertex x := rfl


theorem doubledAlignedState_eq_or_branchSwap_of_vertex_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x y : DoubledAlignedState omega eta)
    (hvertex : doubledAlignedVertex x = doubledAlignedVertex y) :
    y = x ∨ y = doubledAlignedBranchSwap x := by
  have hdart : y.1 = x.1 :=
    orientedDisagreementDart_eq_of_vertex_eq
      homega heta hdegree y.1 x.1 hvertex.symm
  rcases x with ⟨d, firstBranch⟩
  rcases y with ⟨e, secondBranch⟩
  simp only at hdart
  subst e
  cases firstBranch <;> cases secondBranch <;>
    simp [doubledAlignedBranchSwap]

end StatMech.FrontierD
