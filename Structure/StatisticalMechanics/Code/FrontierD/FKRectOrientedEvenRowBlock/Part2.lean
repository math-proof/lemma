/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowBlockRepetition.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part2
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

structure FKRectPositiveRowOrientedBlock
    (R : FKRectTorus) (q : Real) (scale : Nat) where
  block : FKRectOrientedEvenRowBlock R q scale
  row_bound : ∀ v ∈ block.carrier,
    1 ≤ v.2.val ∧ v.2.val ≤ 24 * scale + 4


end
end StatMech.FrontierD
