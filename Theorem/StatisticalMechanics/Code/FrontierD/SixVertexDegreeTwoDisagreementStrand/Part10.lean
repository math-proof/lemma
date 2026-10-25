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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part11
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoStrandStepSeamSign_of_ne_zero
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta)
    (hne : sixVertexDegreeTwoStrandStepSeamSign hdegree d ≠ 0) :
    sixVertexDegreeTwoStrandStepSeamSign hdegree d = 1 ∨
      sixVertexDegreeTwoStrandStepSeamSign hdegree d = -1 := by
  rcases sixVertexTorusEdgeSeamSign_eq_zero_or_one_or_neg_one
    omega eta
    (sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree d.1).1) with hzero | hone | hneg
  · exact False.elim (hne hzero)
  · exact Or.inl hone
  · exact Or.inr hneg


theorem sum_sixVertexDegreeTwoStrandStepSeamSign_eq_edges
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    (∑ d : SixVertexOrientedDisagreementDart omega eta,
        sixVertexDegreeTwoStrandStepSeamSign hdegree d) =
      ∑ e : SixVertexDisagreementEdge omega eta,
        sixVertexTorusEdgeSeamSign omega eta e.1 := by
  let edgeEquiv := sixVertexOrientedDisagreementDartEquivEdge
    homega heta hdegree
  calc
    (∑ d : SixVertexOrientedDisagreementDart omega eta,
        sixVertexDegreeTwoStrandStepSeamSign hdegree d) =
        ∑ d : SixVertexOrientedDisagreementDart omega eta,
          sixVertexTorusEdgeSeamSign omega eta (edgeEquiv d).1 := by
      apply Finset.sum_congr rfl
      intro d hd
      rfl
    _ = ∑ e : SixVertexDisagreementEdge omega eta,
          sixVertexTorusEdgeSeamSign omega eta e.1 :=
      edgeEquiv.sum_comp
        (fun e => sixVertexTorusEdgeSeamSign omega eta e.1)


theorem sum_sixVertexDegreeTwoStrandStepSeamSign_eq_fullTransfer
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    (∑ d : SixVertexOrientedDisagreementDart omega eta,
        sixVertexDegreeTwoStrandStepSeamSign hdegree d) =
      sixVertexTorusMaskSeamTransfer
        (sixVertexFullDisagreementMask omega eta) omega eta := by
  rw [sum_sixVertexDegreeTwoStrandStepSeamSign_eq_edges
      homega heta hdegree,
    sum_sixVertexDisagreementEdge_seamSign,
    sum_sixVertexTorusEdge_seamSign_eq_fullTransfer]


theorem sum_sixVertexDegreeTwoStrandStepSeamSign_eq_two
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    (∑ d : SixVertexOrientedDisagreementDart omega eta,
        sixVertexDegreeTwoStrandStepSeamSign hdegree d) = 2 := by
  rw [sum_sixVertexDegreeTwoStrandStepSeamSign_eq_fullTransfer
    homega heta hdegree]
  exact sixVertexFullDisagreementMask_seamTransfer_eq_two
    omega eta n homegaSector hetaSector hn


end
end StatMech.FrontierD
