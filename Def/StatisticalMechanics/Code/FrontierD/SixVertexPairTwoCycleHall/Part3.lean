/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleHall
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexConfigurationPairTwoCycleFineProfileRelated
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    (source : SixVertexConfigurationPairFineProfileFiber
      T lower upper profile)
    (target : SixVertexConfigurationPairFineProfileFiber
      T middle middle profile) : Prop :=
  SixVertexConfigurationPairTwoCycleFineRelated source.1 target.1


def SixVertexConfigurationPairTwoCycleFineProfileFiberHall
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) : Prop :=
  forall profile : SixVertexHorizontalBoundedFineRowProfile T,
    forall sources : Finset
        (SixVertexConfigurationPairFineProfileFiber
          T lower upper profile),
      sources.card <=
        (Finset.univ.filter fun target :
            SixVertexConfigurationPairFineProfileFiber
              T middle middle profile =>
          ∃ source ∈ sources,
            SixVertexConfigurationPairTwoCycleFineProfileRelated
              source target).card


end
end StatMech.FrontierD
