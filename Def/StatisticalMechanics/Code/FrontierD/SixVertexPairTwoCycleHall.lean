module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
public import Instance.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleHall
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def SixVertexConfigurationPairTwoCycleFineRelated
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (source : SixVertexMarkedPairSource T lower upper)
    (target : SixVertexMarkedPairTarget T middle) : Prop :=
  sixVertexPairAtMostTwoCycleFineRelated
    (source.1.1, source.2.1) (target.1.1, target.2.1)

end
end StatMech.FrontierD
