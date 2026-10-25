/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleHall
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexConfigurationPairTwoCycleFineHall
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) : Prop :=
  forall sources : Finset (SixVertexMarkedPairSource T lower upper),
    sources.card <=
      (Finset.univ.filter fun target : SixVertexMarkedPairTarget T middle =>
        ∃ source ∈ sources,
          SixVertexConfigurationPairTwoCycleFineRelated source target).card


end
end StatMech.FrontierD
