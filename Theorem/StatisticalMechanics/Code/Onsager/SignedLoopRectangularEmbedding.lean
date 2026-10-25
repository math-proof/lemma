/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
import Def.StatisticalMechanics.Code.Onsager.SignedLoopRectangularEmbedding
open Set SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

theorem ons_rectDualIntPoint_injective {M N : Nat} :
    Function.Injective (ons_rectDualIntPoint : ons_RectDualVertex M N -> Int × Int) := by
  intro p q h
  unfold ons_rectDualIntPoint at h
  apply Prod.ext <;> apply Fin.ext
  · have hx := congrArg Prod.fst h
    exact Int.ofNat_inj.mp hx
  · have hy := congrArg Prod.snd h
    exact Int.ofNat_inj.mp hy


end
end StatMech.Onsager
