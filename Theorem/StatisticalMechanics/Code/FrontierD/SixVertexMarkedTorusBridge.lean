/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTorusBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalMarkedDisagreementSwitch
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTorusBridge
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem eval_sixVertexLocalMarkedPatternWeight
    (t : Real) (p : SixVertexLocalIncomingPattern) :
    eval t (sixVertexLocalMarkedPatternWeight p) =
      sixVertexLocalPatternWeight (2 + t) p := by
  unfold sixVertexLocalMarkedPatternWeight sixVertexLocalPatternWeight
  by_cases hp : p.Ice
  · rw [if_pos hp, if_pos hp]
    by_cases hc : p.IsCType <;> simp [hc]
  · simp [hp]


end
end StatMech.FrontierD
