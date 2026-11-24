module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch
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

noncomputable def sixVertexLocalPatternWeight
    (c : Real) (p : SixVertexLocalIncomingPattern) : Real :=
  if p.Ice then if p.IsCType then c else 1 else 0

end
end StatMech.FrontierD
