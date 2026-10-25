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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part17
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoStrandSeamWord_unitSteps
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    ∀ z ∈ sixVertexDegreeTwoStrandSeamWord
        homega heta hdegree seed,
      z = 1 ∨ z = -1 := by
  intro z hz
  simp only [sixVertexDegreeTwoStrandSeamWord, List.mem_filter,
    List.mem_map] at hz
  obtain ⟨⟨d, hd, rfl⟩, hne⟩ := hz
  exact sixVertexDegreeTwoStrandStepSeamSign_of_ne_zero hdegree d
    (of_decide_eq_true hne)

end
end StatMech.FrontierD
