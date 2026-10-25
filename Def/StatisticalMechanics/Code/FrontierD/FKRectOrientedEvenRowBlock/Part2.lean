/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowBlockRepetition.Part2
import Structure.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def FKRectOrientedEvenRowBlock.translate
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectOrientedEvenRowBlock R q scale)
    (offset : Nat) (hoffset : Even offset) :
    FKRectOrientedEvenRowBlock R q scale := by
  let S := fkRectEvenRowTranslationSet R offset B.carrier
  let x : S := fkRectEvenRowTranslationSetEquiv
    R offset B.carrier B.start
  let y : S := fkRectEvenRowTranslationSetEquiv
    R offset B.carrier B.finish
  refine
    { carrier := S
      start := x
      finish := y
      step := B.step
      step_even := B.step_even
      step_scale := B.step_scale
      step_upper := B.step_upper
      translate_start := ?_
      massFloor := B.massFloor
      massFloor_nonneg := B.massFloor_nonneg
      mass_lower := ?_
      column_bound := ?_ }
  · change fkRectEvenRowTranslationVertexEquiv R B.step
        (fkRectEvenRowTranslationVertexEquiv R offset B.start.1) =
      fkRectEvenRowTranslationVertexEquiv R offset B.finish.1
    rw [fkRectEvenRowTranslationVertexEquiv_add, ← B.translate_start,
      fkRectEvenRowTranslationVertexEquiv_add]
    congr 2
    omega
  · rw [show fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega
          B.carrier B.start B.finish} by
      simpa [S, x, y] using
        (fkRectCritical_connectedWithinMass_evenRowTranslation
          R offset hoffset q B.carrier B.start B.finish)]
    exact B.mass_lower
  · intro v hv
    exact (fkRectEvenRowTranslationSet_column_bounds
      R B.carrier offset 0 (4 * scale)
      (fun w hw => ⟨Nat.zero_le _, B.column_bound w hw⟩) hv).2

end
end StatMech.FrontierD
