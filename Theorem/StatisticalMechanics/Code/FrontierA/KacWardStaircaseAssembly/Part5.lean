/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardStaircaseAssembly.Part5


namespace StatMech.FrontierA

open scoped NNReal

open Set


@[simp] theorem KWStairParameterData.vertex_even
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon) (i : Fin n) (k : Fin S) :
    data.vertex (kwStairEvenIndex i k) = data.base i k.castSucc := by
  simp [KWStairParameterData.vertex, kwStairEvenIndex,
    KWStairParameterData.localVertex, kwStairSliceIndex_even]

@[simp] theorem KWStairParameterData.vertex_odd
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon) (i : Fin n) (k : Fin S) :
    data.vertex (kwStairOddIndex i k) = data.corner i k := by
  simp [KWStairParameterData.vertex, kwStairOddIndex,
    KWStairParameterData.localVertex, kwStairSliceIndex_odd]

theorem kwStairEvenIndex_add_one
    {n S : ℕ} [NeZero n] [NeZero S]
    (i : Fin n) (k : Fin S) :
    kwStairEvenIndex i k + 1 = kwStairOddIndex i k := by
  apply Fin.ext
  rw [Fin.val_add]
  have hn : 0 < n := NeZero.pos n
  have hS : 0 < S := NeZero.pos S
  have htotal : 1 < n * (2 * S) := by
    have hnOne : 1 ≤ n := hn
    have htwo : 2 ≤ 2 * S := by omega
    exact lt_of_lt_of_le (by omega : 1 < 1 * 2)
      (Nat.mul_le_mul hnOne htwo)
  have hone : ((1 : Fin (n * (2 * S))).val) = 1 := by
    change 1 % (n * (2 * S)) = 1
    exact Nat.mod_eq_of_lt htotal
  rw [hone]
  simp only [kwStairEvenIndex, kwStairOddIndex, finProdFinEquiv,
    Equiv.coe_fn_mk, kwStairEvenLocal, kwStairOddLocal]
  have hi := i.isLt
  have hk := k.isLt
  have hlocal : 2 * k.val + 1 < 2 * S := by omega
  have hindex : 2 * k.val + 2 * S * i.val + 1 < n * (2 * S) := by
    calc
      2 * k.val + 2 * S * i.val + 1 < 2 * S + 2 * S * i.val := by omega
      _ = (i.val + 1) * (2 * S) := by ring
      _ ≤ n * (2 * S) := Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hi)
  rw [Nat.mod_eq_of_lt hindex]
  omega

theorem kwStairOddIndex_castSucc_add_one
    {n M : ℕ} [NeZero n]
    (i : Fin n) (k : Fin M) :
    kwStairOddIndex (S := M + 1) i k.castSucc + 1 =
      kwStairEvenIndex (S := M + 1) i k.succ := by
  apply Fin.ext
  rw [Fin.val_add]
  have hn : 0 < n := NeZero.pos n
  have htotal : 1 < n * (2 * (M + 1)) := by
    have hnOne : 1 ≤ n := hn
    have htwo : 2 ≤ 2 * (M + 1) := by omega
    exact lt_of_lt_of_le (by omega : 1 < 1 * 2)
      (Nat.mul_le_mul hnOne htwo)
  have hone : ((1 : Fin (n * (2 * (M + 1)))).val) = 1 := by
    change 1 % (n * (2 * (M + 1))) = 1
    exact Nat.mod_eq_of_lt htotal
  rw [hone]
  simp only [kwStairOddIndex, kwStairEvenIndex, finProdFinEquiv,
    Equiv.coe_fn_mk, kwStairOddLocal, kwStairEvenLocal,
    Fin.val_castSucc, Fin.val_succ]
  have hi := i.isLt
  have hk := k.isLt
  have hindex : 2 * k.val + 1 + 2 * (M + 1) * i.val + 1 <
      n * (2 * (M + 1)) := by
    calc
      2 * k.val + 1 + 2 * (M + 1) * i.val + 1 <
          2 * (M + 1) + 2 * (M + 1) * i.val := by omega
      _ = (i.val + 1) * (2 * (M + 1)) := by ring
      _ ≤ n * (2 * (M + 1)) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hi)
  rw [Nat.mod_eq_of_lt hindex]
  omega

theorem kwStairOddIndex_last_add_one
    {n M : ℕ} [NeZero n] (i : Fin n) :
    kwStairOddIndex (S := M + 1) i (Fin.last M) + 1 =
      kwStairEvenIndex (S := M + 1) (i + 1) 0 := by
  apply Fin.ext
  rw [Fin.val_add]
  have hn : 0 < n := NeZero.pos n
  have htotal : 1 < n * (2 * (M + 1)) := by
    have hnOne : 1 ≤ n := hn
    have htwo : 2 ≤ 2 * (M + 1) := by omega
    exact lt_of_lt_of_le (by omega : 1 < 1 * 2)
      (Nat.mul_le_mul hnOne htwo)
  have hone : ((1 : Fin (n * (2 * (M + 1)))).val) = 1 := by
    change 1 % (n * (2 * (M + 1))) = 1
    exact Nat.mod_eq_of_lt htotal
  rw [hone]
  simp only [kwStairOddIndex, kwStairEvenIndex, finProdFinEquiv,
    Equiv.coe_fn_mk, kwStairOddLocal, kwStairEvenLocal,
    Fin.val_last, Fin.val_zero]
  have hi := i.isLt
  by_cases hilast : i.val + 1 < n
  · have hindex : 2 * M + 1 + 2 * (M + 1) * i.val + 1 <
        n * (2 * (M + 1)) := by
      calc
        2 * M + 1 + 2 * (M + 1) * i.val + 1 =
            (i.val + 1) * (2 * (M + 1)) := by ring
        _ < n * (2 * (M + 1)) :=
          Nat.mul_lt_mul_of_pos_right hilast (by omega)
    rw [Nat.mod_eq_of_lt hindex, Fin.val_add_one_of_lt' hilast]
    ring
  · have hieq : i.val + 1 = n := by omega
    have hiwrap : (i + 1 : Fin n).val = 0 := by
      by_cases hnOne : n = 1
      · subst n
        have haddLt := (i + 1 : Fin 1).isLt
        omega
      · have honeLt : 1 < n := by omega
        have honeN : ((1 : Fin n).val) = 1 := by
          change 1 % n = 1
          exact Nat.mod_eq_of_lt honeLt
        rw [Fin.val_add, honeN, hieq, Nat.mod_self]
    rw [hiwrap]
    have hindex : 2 * M + 1 + 2 * (M + 1) * i.val + 1 =
        n * (2 * (M + 1)) := by
      calc
        2 * M + 1 + 2 * (M + 1) * i.val + 1 =
            (i.val + 1) * (2 * (M + 1)) := by ring
        _ = n * (2 * (M + 1)) := congrArg (fun r : ℕ ↦
          r * (2 * (M + 1))) hieq
    rw [hindex, Nat.mod_self]
    simp

@[simp] theorem KWStairParameterData.base_zero
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon) (i : Fin n) :
    data.base i 0 = polygon.vertex i := by
  simp [KWStairParameterData.base, data.parameter_zero]

@[simp] theorem KWStairParameterData.base_last
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon) (i : Fin n) :
    data.base i (Fin.last S) = polygon.vertex (i + 1) := by
  simp [KWStairParameterData.base, data.parameter_last]

theorem KWStairParameterData.vertex_odd_castSucc_succ
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) (k : Fin M) :
    data.vertex (kwStairOddIndex i k.castSucc + 1) =
      data.base i k.succ.castSucc := by
  rw [kwStairOddIndex_castSucc_add_one]
  exact data.vertex_even i k.succ

theorem KWStairParameterData.vertex_odd_last_succ
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) :
    data.vertex (kwStairOddIndex i (Fin.last M) + 1) =
      polygon.vertex (i + 1) := by
  rw [kwStairOddIndex_last_add_one, data.vertex_even]
  exact data.base_zero (i + 1)

theorem lineMap_sub_lineMap
    (a b : ℂ) (s t : ℝ) :
    AffineMap.lineMap a b t - AffineMap.lineMap a b s =
      (t - s) * (b - a) := by
  rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  ring

theorem KWStairParameterData.corner_sub_base
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    data.corner i k - data.base i k.castSucc =
      (data.parameter i k.succ - data.parameter i k.castSucc) *
        kwHorizontalPart (polygon.edgeVector i) := by
  simp [KWStairParameterData.corner]

theorem KWStairParameterData.base_succ_sub_corner
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    data.base i k.succ - data.corner i k =
      (data.parameter i k.succ - data.parameter i k.castSucc) *
        kwVerticalPart (polygon.edgeVector i) := by
  have hbase : data.base i k.succ - data.base i k.castSucc =
      (data.parameter i k.succ - data.parameter i k.castSucc) *
        polygon.edgeVector i := by
    unfold KWStairParameterData.base KWFiniteSimplePolygon.edgeVector
    exact lineMap_sub_lineMap _ _ _ _
  calc
    data.base i k.succ - data.corner i k =
        (data.base i k.succ - data.base i k.castSucc) -
          (data.corner i k - data.base i k.castSucc) := by ring
    _ = (data.parameter i k.succ - data.parameter i k.castSucc) *
          polygon.edgeVector i -
        (data.parameter i k.succ - data.parameter i k.castSucc) *
          kwHorizontalPart (polygon.edgeVector i) := by
      rw [hbase, data.corner_sub_base]
    _ = (data.parameter i k.succ - data.parameter i k.castSucc) *
        kwVerticalPart (polygon.edgeVector i) := by
      have hdecomp := kwHorizontalPart_add_verticalPart
        (polygon.edgeVector i)
      have hdiff : polygon.edgeVector i -
          kwHorizontalPart (polygon.edgeVector i) =
          kwVerticalPart (polygon.edgeVector i) := by
        nth_rewrite 1 [← hdecomp]
        ring
      rw [← mul_sub, hdiff]

theorem KWStairParameterData.vertex_succ_sub_even
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    data.vertex (kwStairEvenIndex i k + 1) -
        data.vertex (kwStairEvenIndex i k) =
      (data.parameter i k.succ - data.parameter i k.castSucc) *
        kwHorizontalPart (polygon.edgeVector i) := by
  rw [kwStairEvenIndex_add_one, data.vertex_odd, data.vertex_even]
  exact data.corner_sub_base i k

theorem KWStairParameterData.vertex_succ_sub_odd_castSucc
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) (k : Fin M) :
    data.vertex (kwStairOddIndex i k.castSucc + 1) -
        data.vertex (kwStairOddIndex i k.castSucc) =
      (data.parameter i k.castSucc.succ -
          data.parameter i k.castSucc.castSucc) *
        kwVerticalPart (polygon.edgeVector i) := by
  rw [kwStairOddIndex_castSucc_add_one, data.vertex_even, data.vertex_odd]
  exact data.base_succ_sub_corner i k.castSucc

theorem KWStairParameterData.vertex_succ_sub_odd_last
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) :
    data.vertex (kwStairOddIndex i (Fin.last M) + 1) -
        data.vertex (kwStairOddIndex i (Fin.last M)) =
      (data.parameter i (Fin.last M).succ -
          data.parameter i (Fin.last M).castSucc) *
        kwVerticalPart (polygon.edgeVector i) := by
  rw [data.vertex_odd_last_succ, data.vertex_odd]
  have h := data.base_succ_sub_corner i (Fin.last M)
  have hlast : (Fin.last M).succ = Fin.last (M + 1) := by
    apply Fin.ext
    rfl
  rw [hlast, data.base_last] at h
  exact h

theorem parameter_eq_of_coordinate_eq
    {a x s t : ℝ} (hx : x ≠ 0) (h : a + s * x = a + t * x) :
    s = t := by
  have hmul : s * x = t * x := add_left_cancel h
  exact mul_right_cancel₀ hx hmul


theorem KWStairParameterData.localVertex_injective
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) : Function.Injective (data.localVertex i) := by
  intro l r hlr
  obtain ⟨k, rfl | rfl⟩ := kwStairLocal_even_or_odd l
  · obtain ⟨q, rfl | rfl⟩ := kwStairLocal_even_or_odd r
    · have hre := congrArg Complex.re hlr
      simp only [data.localVertex_even, data.base_re] at hre
      have ht := parameter_eq_of_coordinate_eq (hcoords i).1 hre
      have hkq : k.castSucc = q.castSucc :=
        (data.parameter_strictMono i).injective ht
      have hkq' : k = q := Fin.castSucc_injective S hkq
      subst q
      rfl
    · have hre := congrArg Complex.re hlr
      have him := congrArg Complex.im hlr
      simp only [data.localVertex_even, data.localVertex_odd,
        data.base_re, data.corner_re] at hre
      simp only [data.localVertex_even, data.localVertex_odd,
        data.base_im, data.corner_im] at him
      have hright := parameter_eq_of_coordinate_eq (hcoords i).1 hre
      have hleft := parameter_eq_of_coordinate_eq (hcoords i).2 him
      have hstrict := data.parameter_strict i q
      linarith
  · obtain ⟨q, rfl | rfl⟩ := kwStairLocal_even_or_odd r
    · have hre := congrArg Complex.re hlr
      have him := congrArg Complex.im hlr
      simp only [data.localVertex_odd, data.localVertex_even,
        data.corner_re, data.base_re] at hre
      simp only [data.localVertex_odd, data.localVertex_even,
        data.corner_im, data.base_im] at him
      have hright := parameter_eq_of_coordinate_eq (hcoords i).1 hre
      have hleft := parameter_eq_of_coordinate_eq (hcoords i).2 him
      have hstrict := data.parameter_strict i k
      linarith
    · have him := congrArg Complex.im hlr
      simp only [data.localVertex_odd, data.corner_im] at him
      have ht := parameter_eq_of_coordinate_eq (hcoords i).2 him
      have hkq : k.castSucc = q.castSucc :=
        (data.parameter_strictMono i).injective ht
      have hkq' : k = q := Fin.castSucc_injective S hkq
      subst q
      rfl


end StatMech.FrontierA
