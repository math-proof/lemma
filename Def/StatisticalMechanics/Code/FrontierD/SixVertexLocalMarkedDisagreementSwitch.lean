module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part6
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceExpansion.Part7
open Finset Matrix Polynomial


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalMarkedDisagreementSwitch.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexLocalMarkedPatternWeight
    (p : SixVertexLocalIncomingPattern) : Real[X] :=
  if p.Ice then if p.IsCType then C 2 + X else 1 else 0

end
end StatMech.FrontierD
