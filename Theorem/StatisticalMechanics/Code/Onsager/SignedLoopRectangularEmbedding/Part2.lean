/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
import Def.StatisticalMechanics.Code.Onsager.SignedLoopRectangularEmbedding.Part2
open Set SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

theorem ons_rectDualComplexPoint_injective {M N : Nat} :
    Function.Injective
      (ons_rectDualComplexPoint : ons_RectDualVertex M N -> Complex) :=
  triangularIntPoint_injective.comp ons_rectDualIntPoint_injective


end
end StatMech.Onsager
