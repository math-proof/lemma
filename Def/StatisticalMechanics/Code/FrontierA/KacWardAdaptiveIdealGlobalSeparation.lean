/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealGlobalSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealLocalSeparation


namespace StatMech.FrontierA

open scoped NNReal

open Set

def kwAdaptiveIdealIndex
    {n M : ℕ} [NeZero n] [NeZero M]
    (i : Fin n) (k : Fin (M + 1)) (even : Bool) :
    Fin (n * (2 * (M + 1))) :=
  if even then kwStairEvenIndex i k else kwStairOddIndex i k

end StatMech.FrontierA
