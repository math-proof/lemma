/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowBlockRepetition.Part2
import Structure.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part2
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectOrientedEvenRowBlockOfReflectedCarrier
    (R : FKRectTorus) (q : Real) (scale : Nat)
    (S : Set R.Vertex) (x y : S)
    (hspan : (scale : Int) ≤
      2 * |(y.1.2.val : Int) - x.1.2.val| + 2)
    (hrows : x.1.2.val ≤ 8 * scale + 1 ∧
      y.1.2.val ≤ 8 * scale + 1)
    {massFloor : Real} (hmassFloor : 0 ≤ massFloor)
    (hlower : massFloor ≤
      fkRectCriticalEventMass R q
        (fkRectReflectedCarrierConnectionEvent R S x y))
    (hcolumns : ∀ v ∈
      S ∪ fkRectDevelopedReflectionSet R y.1.2.val S,
      v.1.val ≤ 4 * scale) :
    FKRectOrientedEvenRowBlock R q scale := by
  let Sr := fkRectDevelopedReflectionSet R y.1.2.val S
  let U : Set R.Vertex := S ∪ Sr
  let xU : U := ⟨x.1, Or.inl x.2⟩
  let xr : R.Vertex :=
    fkRectDevelopedReflectionVertexEquiv R y.1.2.val x.1
  let xrU : U := ⟨xr, Or.inr ⟨x.1, x.2, rfl⟩⟩
  let step := fkRectReflectedRowStep x.1.2.val y.1.2.val
  have hstepCast : (step : Int) =
      2 * |(y.1.2.val : Int) - x.1.2.val| :=
    fkRectReflectedRowStep_cast _ _
  have hstepScale : scale ≤ step + 2 := by
    have hspan' : (scale : Int) ≤ (step : Int) + 2 := by
      rw [hstepCast]
      exact hspan
    exact_mod_cast hspan'
  have hstepUpper : step ≤ 16 * scale + 2 := by
    rw [show step = fkRectReflectedRowStep
      x.1.2.val y.1.2.val by rfl]
    rw [← Int.ofNat_le]
    rw [fkRectReflectedRowStep_cast]
    by_cases hxy : x.1.2.val ≤ y.1.2.val
    · rw [abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_nonpos (by omega)]
      omega
  by_cases hxy : x.1.2.val ≤ y.1.2.val
  · refine
      { carrier := U
        start := xU
        finish := xrU
        step := step
        step_even := fkRectReflectedRowStep_even _ _
        step_scale := hstepScale
        step_upper := hstepUpper
        translate_start := ?_
        massFloor := massFloor
        massFloor_nonneg := hmassFloor
        mass_lower := ?_
        column_bound := ?_ }
    · exact fkRectEvenRowTranslation_reflection_of_row_le
        R x.1 y.1 hxy
    · simpa [U, Sr, xU, xrU, xr,
        fkRectReflectedCarrierConnectionEvent] using hlower
    · intro v hv
      exact hcolumns v hv
  · have hyx : y.1.2.val ≤ x.1.2.val := by omega
    refine
      { carrier := U
        start := xrU
        finish := xU
        step := step
        step_even := fkRectReflectedRowStep_even _ _
        step_scale := hstepScale
        step_upper := hstepUpper
        translate_start := ?_
        massFloor := massFloor
        massFloor_nonneg := hmassFloor
        mass_lower := ?_
        column_bound := ?_ }
    · exact fkRectEvenRowTranslation_reflection_of_row_ge
        R x.1 y.1 hyx
    · have hevent :
          {omega | FKRectConnectedWithin R omega U xrU xU} =
            {omega | FKRectConnectedWithin R omega U xU xrU} := by
        ext omega
        exact SimpleGraph.reachable_comm
      rw [hevent]
      simpa [U, Sr, xU, xrU, xr,
        fkRectReflectedCarrierConnectionEvent] using hlower
    · intro v hv
      exact hcolumns v hv

end
end StatMech.FrontierD
