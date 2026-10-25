/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple
import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptivePatchedWalk.Part6


namespace StatMech.FrontierA

open Set

@[simp] theorem KWAdaptivePatchedData.vertex_even
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    patch.vertex (kwStairEvenIndex i k) = patch.pathBase i k := by
  simp [KWAdaptivePatchedData.vertex, kwStairEvenIndex]

@[simp] theorem KWAdaptivePatchedData.vertex_odd
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    patch.vertex (kwStairOddIndex i k) = patch.pathCorner i k := by
  simp [KWAdaptivePatchedData.vertex, kwStairOddIndex]

theorem KWAdaptivePatchedData.incomingPort_eq
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) :
    patch.incomingPort i = polygon.vertex (i + 1) +
      patch.alpha (i + 1) * (-polygon.edgeVector i) := by
  unfold KWAdaptivePatchedData.incomingPort
  rw [patch.data.base_penultimate_eq_incomingPatchBase i
    (patch.alpha (i + 1)) (patch.parameter_penultimate i)]
  rfl

theorem KWAdaptivePatchedData.outgoingPort_eq
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) :
    patch.outgoingPort i = polygon.vertex i +
      patch.beta * polygon.edgeVector i := by
  unfold KWAdaptivePatchedData.outgoingPort
  rw [patch.data.base_one_eq_outgoingPatchEnd i patch.beta
    (patch.parameter_one i)]
  rfl

theorem KWAdaptivePatchedData.middleCorner_sub_base
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.middleCorner i q -
        patch.data.base i q.succ.castSucc.castSucc =
      (patch.data.parameter i q.succ.castSucc.succ -
        patch.data.parameter i q.succ.castSucc.castSucc) *
        (if patch.sliceUsesVerticalFirst i q then
          kwVerticalPart (polygon.edgeVector i)
        else kwHorizontalPart (polygon.edgeVector i)) := by
  by_cases hv : patch.sliceUsesVerticalFirst i q
  · simp [KWAdaptivePatchedData.middleCorner, hv]
  · simp only [KWAdaptivePatchedData.middleCorner, hv, if_false]
    exact patch.data.corner_sub_base i q.succ.castSucc

theorem KWAdaptivePatchedData.base_succ_sub_middleCorner
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.data.base i q.succ.castSucc.succ - patch.middleCorner i q =
      (patch.data.parameter i q.succ.castSucc.succ -
        patch.data.parameter i q.succ.castSucc.castSucc) *
        (if patch.sliceUsesVerticalFirst i q then
          kwHorizontalPart (polygon.edgeVector i)
        else kwVerticalPart (polygon.edgeVector i)) := by
  by_cases hv : patch.sliceUsesVerticalFirst i q
  · simp only [KWAdaptivePatchedData.middleCorner, hv, if_true]
    have hbase : patch.data.base i q.succ.castSucc.succ -
        patch.data.base i q.succ.castSucc.castSucc =
      (patch.data.parameter i q.succ.castSucc.succ -
        patch.data.parameter i q.succ.castSucc.castSucc) *
          polygon.edgeVector i := by
      unfold KWStairParameterData.base KWFiniteSimplePolygon.edgeVector
      exact lineMap_sub_lineMap _ _ _ _
    rw [show patch.data.base i q.succ.castSucc.succ -
          (patch.data.base i q.succ.castSucc.castSucc +
            (patch.data.parameter i q.succ.castSucc.succ -
              patch.data.parameter i q.succ.castSucc.castSucc) *
                kwVerticalPart (polygon.edgeVector i)) =
        (patch.data.base i q.succ.castSucc.succ -
          patch.data.base i q.succ.castSucc.castSucc) -
            (patch.data.parameter i q.succ.castSucc.succ -
              patch.data.parameter i q.succ.castSucc.castSucc) *
                kwVerticalPart (polygon.edgeVector i) by ring,
      hbase]
    rw [← mul_sub]
    have hdecomp := kwHorizontalPart_add_verticalPart
      (polygon.edgeVector i)
    have : polygon.edgeVector i - kwVerticalPart (polygon.edgeVector i) =
        kwHorizontalPart (polygon.edgeVector i) := by
      nth_rewrite 1 [← hdecomp]
      ring
    rw [this]
  · simp only [KWAdaptivePatchedData.middleCorner, hv, if_false]
    exact patch.data.base_succ_sub_corner i q.succ.castSucc


theorem KWAdaptivePatchedData.rawEdge_even_castSucc
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    kwRawEdge patch.vertex (kwStairEvenIndex i q.castSucc) =
      (patch.data.parameter i q.succ.castSucc.succ -
        patch.data.parameter i q.succ.castSucc.castSucc) *
        (if patch.sliceUsesVerticalFirst i q then
          kwVerticalPart (polygon.edgeVector i)
        else kwHorizontalPart (polygon.edgeVector i)) := by
  unfold kwRawEdge
  rw [kwStairEvenIndex_add_one, patch.vertex_even, patch.vertex_odd,
    patch.pathBase_castSucc, patch.pathCorner_castSucc]
  exact patch.middleCorner_sub_base i q


theorem KWAdaptivePatchedData.rawEdge_odd_castSucc
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    kwRawEdge patch.vertex (kwStairOddIndex i q.castSucc) =
      (patch.data.parameter i q.succ.castSucc.succ -
        patch.data.parameter i q.succ.castSucc.castSucc) *
        (if patch.sliceUsesVerticalFirst i q then
          kwHorizontalPart (polygon.edgeVector i)
        else kwVerticalPart (polygon.edgeVector i)) := by
  unfold kwRawEdge
  rw [kwStairOddIndex_castSucc_add_one, patch.vertex_even, patch.vertex_odd,
    patch.pathCorner_castSucc]
  have hbase : patch.pathBase i q.succ =
      patch.data.base i q.succ.castSucc.succ := by
    by_cases hq : q = patch.lastMiddleIndex
    · subst q
      have hlast : patch.lastMiddleIndex.succ = Fin.last M := by
        apply Fin.ext
        simp [KWAdaptivePatchedData.lastMiddleIndex]
        have := patch.hM
        omega
      rw [hlast, patch.pathBase_last]
      unfold KWAdaptivePatchedData.incomingPort
      congr 2
    · have hsucc_ne : q.succ ≠ Fin.last M := by
        intro h
        apply hq
        apply Fin.ext
        have hval := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_last] at hval
        simp [KWAdaptivePatchedData.lastMiddleIndex]
        omega
      obtain ⟨r, hr⟩ := Fin.eq_castSucc_of_ne_last hsucc_ne
      rw [← hr, patch.pathBase_castSucc]
      congr 2
  rw [hbase]
  exact patch.base_succ_sub_middleCorner i q


theorem KWAdaptivePatchedData.rawEdge_even_last
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) :
    kwRawEdge patch.vertex (kwStairEvenIndex i (Fin.last M)) =
      (patch.connector (i + 1)).corner -
        patch.alpha (i + 1) * (-polygon.edgeVector i) := by
  unfold kwRawEdge
  rw [kwStairEvenIndex_add_one, patch.vertex_even, patch.vertex_odd,
    patch.pathBase_last, patch.pathCorner_last, patch.incomingPort_eq]
  unfold KWAdaptivePatchedData.connectorCorner
  ring


theorem KWAdaptivePatchedData.rawEdge_odd_last
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) :
    kwRawEdge patch.vertex (kwStairOddIndex i (Fin.last M)) =
      patch.beta * polygon.edgeVector (i + 1) -
        (patch.connector (i + 1)).corner := by
  unfold kwRawEdge
  rw [kwStairOddIndex_last_add_one, patch.vertex_odd, patch.vertex_even,
    patch.pathCorner_last]
  have hzero : (0 : Fin (M + 1)) = (0 : Fin M).castSucc := by
    apply Fin.ext
    rfl
  rw [hzero, patch.pathBase_castSucc]
  have hport : patch.data.base (i + 1)
      (0 : Fin M).succ.castSucc.castSucc = patch.outgoingPort (i + 1) := by
    unfold KWAdaptivePatchedData.outgoingPort
    congr 2
  rw [hport, patch.outgoingPort_eq]
  unfold KWAdaptivePatchedData.connectorCorner
  ring

end StatMech.FrontierA
