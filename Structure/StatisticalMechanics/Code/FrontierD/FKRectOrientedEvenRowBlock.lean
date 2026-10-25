/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowBlockRepetition.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

structure FKRectOrientedEvenRowBlock
    (R : FKRectTorus) (q : Real) (scale : Nat) where
  carrier : Set R.Vertex
  start : carrier
  finish : carrier
  step : Nat
  step_even : Even step
  step_scale : scale ≤ step + 2
  step_upper : step ≤ 16 * scale + 2
  translate_start :
    fkRectEvenRowTranslationVertexEquiv R step start.1 = finish.1
  massFloor : Real
  massFloor_nonneg : 0 ≤ massFloor
  mass_lower : massFloor ≤
    fkRectCriticalEventMass R q
      {omega | FKRectConnectedWithin R omega carrier start finish}
  column_bound : ∀ v ∈ carrier, v.1.val ≤ 4 * scale


end
end StatMech.FrontierD
