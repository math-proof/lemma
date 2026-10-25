/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
import Mathlib.Data.List.Rotate
import Def.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part4


namespace StatMech.FrontierA

@[simp] theorem KWFiniteSimplePolygon.edgeVector_eq_cyclic
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n) :
    polygon.edgeVector i = kwCyclicEdgeVector polygon.vertex i := rfl

@[simp] theorem KWFiniteSimplePolygon.edgeList_eq_cyclic
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    polygon.edgeList = kwCyclicEdgeList polygon.vertex := rfl

@[simp] theorem KWFiniteSimplePolygon.rotate_edgeVector
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (r i : Fin n) :
    (polygon.rotate r).edgeVector i = polygon.edgeVector (i + r) := by
  unfold KWFiniteSimplePolygon.edgeVector KWFiniteSimplePolygon.rotate
  dsimp only
  congr 2
  abel


theorem KWFiniteSimplePolygon.rotate_not_collinear
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (r : Fin n) :
    ∀ i : Fin n, ¬Collinear ℝ
      ({(polygon.rotate r).vertex i,
        (polygon.rotate r).vertex (i + 1),
        (polygon.rotate r).vertex (i + 2)} : Set ℂ) := by
  intro i
  change ¬Collinear ℝ
    ({polygon.vertex (i + r), polygon.vertex (i + 1 + r),
      polygon.vertex (i + 2 + r)} : Set ℂ)
  have h1 : i + 1 + r = (i + r) + 1 := by abel
  have h2 : i + 2 + r = (i + r) + 2 := by abel
  rw [h1, h2]
  exact hnoncollinear (i + r)

theorem KWFiniteSimplePolygon.rotate_edgeList
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (r : Fin n) :
    (polygon.rotate r).edgeList = polygon.edgeList.rotate r.val := by
  change List.ofFn (polygon.rotate r).edgeVector =
    (List.ofFn polygon.edgeVector).rotate r.val
  apply List.ext_getElem
  · simp
  · intro i hiLeft hiRight
    rw [List.getElem_ofFn, List.getElem_rotate]
    simp only [List.length_ofFn, List.getElem_ofFn,
      KWFiniteSimplePolygon.rotate_edgeVector]
    congr 2

theorem KWFiniteSimplePolygon.edgeVector_ne_zero
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n) :
    polygon.edgeVector i ≠ 0 := by
  rw [KWFiniteSimplePolygon.edgeVector, sub_ne_zero]
  apply polygon.vertex_injective.ne
  intro hindex
  have hzeroOne : (0 : Fin n) = 1 := by
    apply add_left_cancel (a := i)
    simpa using hindex.symm
  have hval := congrArg Fin.val hzeroOne
  have hn : 3 ≤ n := polygon.three_le
  simp [Nat.mod_eq_of_lt (by omega : 1 < n)] at hval


theorem KWFiniteSimplePolygon.quadrilateral_edge_sum
    (polygon : KWFiniteSimplePolygon 4) (i : Fin 4) :
    polygon.edgeVector i + polygon.edgeVector (i + 1) +
        polygon.edgeVector (i + 2) + polygon.edgeVector (i + 3) = 0 := by
  have h11 : i + 1 + 1 = i + 2 := by abel
  have h21 : i + 2 + 1 = i + 3 := by abel
  have h31 : i + 3 + 1 = i := by
    rw [add_assoc]
    have h : (3 : Fin 4) + 1 = 0 := by decide
    rw [h, add_zero]
  simp only [KWFiniteSimplePolygon.edgeVector, h11, h21, h31]
  ring


theorem KWFiniteSimplePolygon.edge_cross_ne_zero_of_not_collinear
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) (i : Fin n) :
    kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0 := by
  intro hzero
  apply hnoncollinear i
  apply kw_collinear_of_cross_sub_eq_zero
  have hidx : i + 1 + 1 = i + 2 := by
    rw [add_assoc]
    congr 1
    apply Fin.ext
    have hthree := polygon.three_le
    have hn : 2 < n := by omega
    simp [Fin.val_add, Nat.mod_eq_of_lt hn]
  simpa only [KWFiniteSimplePolygon.edgeVector, hidx] using hzero


theorem KWFiniteSimplePolygon.quadrilateral_not_cross_pattern_zero_two
    (polygon : KWFiniteSimplePolygon 4) :
    ¬(kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) *
          kwComplexCross (polygon.edgeVector 3) (polygon.edgeVector 0) < 0 ∧
      kwComplexCross (polygon.edgeVector 1) (polygon.edgeVector 2) *
          kwComplexCross (polygon.edgeVector 2) (polygon.edgeVector 3) < 0) := by
  rintro ⟨hAB, hCD⟩
  have he0 : polygon.edgeVector 0 =
      polygon.vertex 1 - polygon.vertex 0 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he1 : polygon.edgeVector 1 =
      polygon.vertex 2 - polygon.vertex 1 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he2 : polygon.edgeVector 2 =
      polygon.vertex 3 - polygon.vertex 2 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he3 : polygon.edgeVector 3 =
      polygon.vertex 0 - polygon.vertex 3 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  simp only [he0, he1, he2, he3] at hAB hCD
  have hcross := kw_exists_common_sbtw_of_cross_opposite
    (A := polygon.vertex 0) (B := polygon.vertex 1)
    (C := polygon.vertex 2) (D := polygon.vertex 3) (by
      convert hAB using 1 <;>
        unfold kwComplexCross <;>
        simp only [Complex.sub_re, Complex.sub_im] <;>
        ring) (by
      convert hCD using 1 <;>
        unfold kwComplexCross <;>
        simp only [Complex.sub_re, Complex.sub_im] <;>
        ring)
  obtain ⟨z, hz0, hz2⟩ := hcross
  exact Set.disjoint_left.mp
    (polygon.edgeInteriors_disjoint 0 2 (by decide)) hz0 hz2


theorem KWFiniteSimplePolygon.quadrilateral_not_cross_pattern_one_three
    (polygon : KWFiniteSimplePolygon 4) :
    ¬(kwComplexCross (polygon.edgeVector 1) (polygon.edgeVector 2) *
          kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) < 0 ∧
      kwComplexCross (polygon.edgeVector 2) (polygon.edgeVector 3) *
          kwComplexCross (polygon.edgeVector 3) (polygon.edgeVector 0) < 0) := by
  rintro ⟨hAB, hCD⟩
  have he0 : polygon.edgeVector 0 =
      polygon.vertex 1 - polygon.vertex 0 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he1 : polygon.edgeVector 1 =
      polygon.vertex 2 - polygon.vertex 1 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he2 : polygon.edgeVector 2 =
      polygon.vertex 3 - polygon.vertex 2 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he3 : polygon.edgeVector 3 =
      polygon.vertex 0 - polygon.vertex 3 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  simp only [he0, he1, he2, he3] at hAB hCD
  have hcross := kw_exists_common_sbtw_of_cross_opposite
    (A := polygon.vertex 1) (B := polygon.vertex 2)
    (C := polygon.vertex 3) (D := polygon.vertex 0) (by
      convert hAB using 1 <;>
        unfold kwComplexCross <;>
        simp only [Complex.sub_re, Complex.sub_im] <;>
        ring) (by
      convert hCD using 1 <;>
        unfold kwComplexCross <;>
        simp only [Complex.sub_re, Complex.sub_im] <;>
        ring)
  obtain ⟨z, hz1, hz3⟩ := hcross
  exact Set.disjoint_left.mp
    (polygon.edgeInteriors_disjoint 1 3 (by decide)) hz1 hz3

theorem KWFiniteSimplePolygon.add_one_ne_self
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n) :
    i + 1 ≠ i := by
  intro h
  have h10 : (1 : Fin n) = 0 := by
    apply add_left_cancel (a := i)
    simpa using h
  have hval := congrArg Fin.val h10
  have hthree := polygon.three_le
  simp [Nat.mod_eq_of_lt (by omega : 1 < n)] at hval

theorem KWFiniteSimplePolygon.add_two_ne_self
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n) :
    i + 2 ≠ i := by
  intro h
  have h20 : (2 : Fin n) = 0 := by
    apply add_left_cancel (a := i)
    simpa using h
  have hval := congrArg Fin.val h20
  have hthree := polygon.three_le
  simp [Nat.mod_eq_of_lt (by omega : 2 < n)] at hval

theorem KWFiniteSimplePolygon.add_two_ne_add_one
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n) :
    i + 2 ≠ i + 1 := by
  intro h
  have h21 : (2 : Fin n) = 1 := by
    apply add_left_cancel (a := i)
    simpa using h
  have hval := congrArg Fin.val h21
  have hthree := polygon.three_le
  have h1 : 1 < n := by omega
  have h2 : 2 < n := by omega
  simp [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval


theorem KWFiniteSimplePolygon.consecutive_wbtw_of_collinear
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n)
    (hcol : Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    Wbtw ℝ (polygon.vertex i) (polygon.vertex (i + 1))
      (polygon.vertex (i + 2)) := by
  have hi1 := polygon.add_one_ne_self i
  have hi2 := polygon.add_two_ne_self i
  have h21 := polygon.add_two_ne_add_one i
  have h01 : polygon.vertex i ≠ polygon.vertex (i + 1) :=
    polygon.vertex_injective.ne hi1.symm
  have h02 : polygon.vertex i ≠ polygon.vertex (i + 2) :=
    polygon.vertex_injective.ne hi2.symm
  have h12 : polygon.vertex (i + 1) ≠ polygon.vertex (i + 2) :=
    polygon.vertex_injective.ne h21.symm
  rcases hcol.wbtw_or_wbtw_or_wbtw with hmid | hmid | hmid
  · exact hmid
  · exfalso
    have hstrict : Sbtw ℝ (polygon.vertex i)
        (polygon.vertex (i + 2)) (polygon.vertex (i + 1)) :=
      ⟨hmid.symm, h02.symm, h12.symm⟩
    exact polygon.vertex_not_strictly_between i (i + 2)
      hi2 h21 (by simpa using hstrict)
  · exfalso
    have hstrict : Sbtw ℝ (polygon.vertex (i + 1))
        (polygon.vertex i) (polygon.vertex (i + 2)) :=
      ⟨hmid.symm, h01, h02⟩
    exact polygon.vertex_not_strictly_between (i + 1) i
      hi1.symm (by
        have hidx : i + 1 + 1 = i + 2 := by
          rw [add_assoc]
          congr 1
          apply Fin.ext
          have hthree := polygon.three_le
          have hn : 2 < n := by omega
          simp [Fin.val_add, Nat.mod_eq_of_lt hn]
        rw [hidx]
        exact hi2.symm)
      (by
        have hidx : i + 1 + 1 = i + 2 := by
          rw [add_assoc]
          congr 1
          apply Fin.ext
          have hthree := polygon.three_le
          have hn : 2 < n := by omega
          simp [Fin.val_add, Nat.mod_eq_of_lt hn]
        simpa only [hidx] using hstrict)


theorem KWFiniteSimplePolygon.not_sbtw_zero_two_of_between
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hbetween : Wbtw ℝ (polygon.vertex 0) (polygon.vertex 1)
      (polygon.vertex 2))
    (k : Fin n) (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hk2 : k ≠ 2) :
    ¬Sbtw ℝ (polygon.vertex 0) (polygon.vertex k) (polygon.vertex 2) := by
  intro hk
  have h01idx : (0 : Fin n) + 1 = 1 := by
    apply Fin.ext
    have hthree := polygon.three_le
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have h12idx : (1 : Fin n) + 1 = 2 := by
    apply Fin.ext
    have hthree := polygon.three_le
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < n)]
  have h02 : polygon.vertex 0 ≠ polygon.vertex 2 :=
    polygon.vertex_injective.ne (by
      simpa only [zero_add] using (polygon.add_two_ne_self 0).symm)
  have h01 : polygon.vertex 0 ≠ polygon.vertex 1 :=
    polygon.vertex_injective.ne (by
      simpa only [zero_add] using (polygon.add_one_ne_self 0).symm)
  have h12 : polygon.vertex 1 ≠ polygon.vertex 2 :=
    polygon.vertex_injective.ne (by
      simpa only [zero_add] using (polygon.add_two_ne_add_one 0).symm)
  rcases kw_sbtw_eq_or_sbtw_or_sbtw h02 h01 h12 hbetween hk with
      heq | hk01 | hk12
  · exact hk1 (polygon.vertex_injective heq)
  · exact polygon.vertex_not_strictly_between 0 k
      hk0 (by simpa only [h01idx] using hk1)
      (by simpa only [h01idx] using hk01)
  · exact polygon.vertex_not_strictly_between 1 k
      hk1 (by simpa only [h12idx] using hk2)
      (by simpa only [h12idx] using hk12)


theorem KWFiniteSimplePolygon.diagonal_zero_two_disjoint
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hbetween : Wbtw ℝ (polygon.vertex 0) (polygon.vertex 1)
      (polygon.vertex 2))
    (k : Fin n) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    Disjoint
      {z : ℂ | Sbtw ℝ (polygon.vertex 0) z (polygon.vertex 2)}
      {z : ℂ | Sbtw ℝ (polygon.vertex k) z (polygon.vertex (k + 1))} := by
  rw [Set.disjoint_left]
  intro z hzdiag hzk
  have h01idx : (0 : Fin n) + 1 = 1 := by
    apply Fin.ext
    have hthree := polygon.three_le
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have h12idx : (1 : Fin n) + 1 = 2 := by
    apply Fin.ext
    have hthree := polygon.three_le
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < n)]
  have h02 : polygon.vertex 0 ≠ polygon.vertex 2 :=
    polygon.vertex_injective.ne (by
      simpa only [zero_add] using (polygon.add_two_ne_self 0).symm)
  have h01 : polygon.vertex 0 ≠ polygon.vertex 1 :=
    polygon.vertex_injective.ne (by
      simpa only [zero_add] using (polygon.add_one_ne_self 0).symm)
  have h12 : polygon.vertex 1 ≠ polygon.vertex 2 :=
    polygon.vertex_injective.ne (by
      simpa only [zero_add] using (polygon.add_two_ne_add_one 0).symm)
  rcases kw_sbtw_eq_or_sbtw_or_sbtw h02 h01 h12 hbetween hzdiag with
      rfl | hz01 | hz12
  · have hkSucc : (1 : Fin n) ≠ k + 1 := by
      intro h
      apply hk0
      apply add_right_cancel (b := (1 : Fin n))
      simpa using h.symm
    exact polygon.vertex_not_strictly_between k 1 hk1.symm hkSucc hzk
  · exact (Set.disjoint_left.mp
      (polygon.edgeInteriors_disjoint 0 k hk0.symm))
        (by simpa only [h01idx] using hz01) hzk
  · exact (Set.disjoint_left.mp
      (polygon.edgeInteriors_disjoint 1 k hk1.symm))
        (by simpa only [h12idx] using hz12) hzk


end StatMech.FrontierA
