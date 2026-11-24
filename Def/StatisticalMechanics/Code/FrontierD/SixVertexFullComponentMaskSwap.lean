module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopLexUnitFineRelation
public import Instance.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def SixVertexFullDisagreementMask
    {T : EvenTorus} (omega eta mask : SixVertexArrows T) : Prop :=
  (forall v d, sixVertexTorusLocalSwitchMask mask v d = true ->
    sixVertexLocalIncomingPattern omega v d ≠
      sixVertexLocalIncomingPattern eta v d) /\
  (forall v d r, sixVertexTorusLocalSwitchMask mask v d = true ->
    sixVertexLocalIncomingPattern omega v r ≠
      sixVertexLocalIncomingPattern eta v r ->
    sixVertexTorusLocalSwitchMask mask v r = true)

end
end StatMech.FrontierD
