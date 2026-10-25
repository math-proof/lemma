/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowBlockRepetition.Part2
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectReflectedRowStep (x y : Nat) : Nat :=
  2 * Int.natAbs ((y : Int) - x)

end
end StatMech.FrontierD
