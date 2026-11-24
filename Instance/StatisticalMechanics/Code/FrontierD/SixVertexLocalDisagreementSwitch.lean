module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

instance (p : SixVertexLocalIncomingPattern) :
    Decidable p.Ice := by
  unfold SixVertexLocalIncomingPattern.Ice
  exact inferInstance

instance (p : SixVertexLocalIncomingPattern) :
    Decidable p.IsCType := by
  unfold SixVertexLocalIncomingPattern.IsCType
  exact inferInstance

end
end StatMech.FrontierD
