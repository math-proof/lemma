/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowBlockRepetition.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part2
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem FKRectOrientedEvenRowBlock.translate_carrier
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectOrientedEvenRowBlock R q scale)
    (offset : Nat) (hoffset : Even offset) :
    (B.translate offset hoffset).carrier =
      fkRectEvenRowTranslationSet R offset B.carrier := rfl

@[simp] theorem FKRectOrientedEvenRowBlock.translate_massFloor
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectOrientedEvenRowBlock R q scale)
    (offset : Nat) (hoffset : Even offset) :
    (B.translate offset hoffset).massFloor = B.massFloor := rfl


end
end StatMech.FrontierD
