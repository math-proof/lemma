/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardStaircaseAssembly.Part4


namespace StatMech.FrontierA

open scoped NNReal

open Set


@[simp] theorem KWStairParameterData.localVertex_even
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    data.localVertex i (kwStairEvenLocal k) = data.base i k.castSucc := by
  simp [KWStairParameterData.localVertex, kwStairSliceIndex_even]

@[simp] theorem KWStairParameterData.localVertex_odd
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    data.localVertex i (kwStairOddLocal k) = data.corner i k := by
  simp [KWStairParameterData.localVertex, kwStairSliceIndex_odd]

theorem kwStairLocal_even_or_odd
    {S : ℕ} [NeZero S] (l : Fin (2 * S)) :
    ∃ k : Fin S, l = kwStairEvenLocal k ∨ l = kwStairOddLocal k := by
  let k := kwStairSliceIndex l
  refine ⟨k, ?_⟩
  have hdiv := Nat.mod_add_div l.val 2
  rcases Nat.mod_two_eq_zero_or_one l.val with heven | hodd
  · left
    apply Fin.ext
    dsimp only [k, kwStairSliceIndex, kwStairEvenLocal]
    omega
  · right
    apply Fin.ext
    dsimp only [k, kwStairSliceIndex, kwStairOddLocal]
    omega

theorem KWStairParameterData.base_re
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin (S + 1)) :
    (data.base i k).re = (polygon.vertex i).re +
      data.parameter i k * (polygon.edgeVector i).re := by
  unfold KWStairParameterData.base KWFiniteSimplePolygon.edgeVector
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul,
    Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem KWStairParameterData.base_im
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin (S + 1)) :
    (data.base i k).im = (polygon.vertex i).im +
      data.parameter i k * (polygon.edgeVector i).im := by
  unfold KWStairParameterData.base KWFiniteSimplePolygon.edgeVector
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul,
    Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem KWStairParameterData.corner_re
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    (data.corner i k).re = (polygon.vertex i).re +
      data.parameter i k.succ * (polygon.edgeVector i).re := by
  rw [KWStairParameterData.corner, Complex.add_re, data.base_re]
  simp only [kwHorizontalPart, Complex.mul_re, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem KWStairParameterData.corner_im
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    (data.corner i k).im = (polygon.vertex i).im +
      data.parameter i k.castSucc * (polygon.edgeVector i).im := by
  rw [KWStairParameterData.corner, Complex.add_im, data.base_im]
  simp only [kwHorizontalPart, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    mul_zero, sub_zero, add_zero]

end StatMech.FrontierA
