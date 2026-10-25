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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoAllStrandsSeamWord_unitSteps
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    ∀ z ∈ sixVertexDegreeTwoAllStrandsSeamWord
        homega heta hdegree,
      z = 1 ∨ z = -1 := by
  intro z hz
  simp only [sixVertexDegreeTwoAllStrandsSeamWord,
    List.mem_filter, List.mem_map] at hz
  obtain ⟨⟨d, hd, rfl⟩, hne⟩ := hz
  exact sixVertexDegreeTwoStrandStepSeamSign_of_ne_zero hdegree d
    (ne_zero_of_intKeepNonzero _ hne)


theorem sixVertexDegreeTwoAllStrandsSeamWord_sum_eq_two
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    (sixVertexDegreeTwoAllStrandsSeamWord
      homega heta hdegree).sum = 2 := by
  unfold sixVertexDegreeTwoAllStrandsSeamWord
  rw [sum_filter_intKeepNonzero,
    sum_map_sixVertexDegreeTwoOrderedAllStrands]
  exact sum_sixVertexDegreeTwoStrandStepSeamSign_eq_two
    homega heta hdegree n homegaSector hetaSector hn

end
end StatMech.FrontierD
