/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoOrderedStrand
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    List (SixVertexOrientedDisagreementDart omega eta) :=
  let sigma := sixVertexOrientedDegreeTwoStrandSuccessor
    homega heta hdegree
  let cycle := sigma.cycleOf seed
  List.ofFn fun k : Fin (orderOf cycle) => (sigma ^ k.val) seed


noncomputable def sixVertexDegreeTwoStrandSeamWord
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) : List Int :=
  ((sixVertexDegreeTwoOrderedStrand homega heta hdegree seed).map
      (sixVertexDegreeTwoStrandStepSeamSign hdegree)).filter
    fun z => z ≠ 0


end
end StatMech.FrontierD
