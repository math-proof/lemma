/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneExponentBounds
open Finset


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

open StatMech StatMech.Ising

theorem eval_foldl_add_apply (X Y : Real) (f : Nat -> BiPoly)
    (xs : List Nat) (p : BiPoly) :
    (xs.foldl (fun p x => p.add (f x)) p).eval X Y =
      p.eval X Y + (xs.map fun x => (f x).eval X Y).sum := by
  induction xs generalizing p with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      change (p + f x).eval X Y + _ = _
      rw [BiPoly.eval_add]
      simp only [List.map_cons, List.sum_cons]
      ring

theorem list_range_sum_eq_finset_range_sum
    (f : Nat -> Real) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem BiPoly.eval_sumCodes (X Y : Real) (f : Nat -> BiPoly) :
    (BiPoly.sumCodes f).eval X Y =
      ((List.range 512).map fun s => (f s).eval X Y).sum := by
  unfold BiPoly.sumCodes
  rw [eval_foldl_add_apply]
  simp

theorem BiPoly.eval_sumCodes_eq_fin_sum (X Y : Real) (f : Nat -> BiPoly) :
    (BiPoly.sumCodes f).eval X Y =
      ∑ s : Fin 512, (f s).eval X Y := by
  rw [BiPoly.eval_sumCodes, list_range_sum_eq_finset_range_sum]
  exact (Fin.sum_univ_eq_sum_range
    (fun s : Nat => (f s).eval X Y) 512).symm

theorem spinCode_odd (s k : Nat) : Odd (spinCode s k) := by
  unfold spinCode
  split <;> norm_num

theorem odd_sum_nine
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 : Int}
    (h0 : Odd a0) (h1 : Odd a1) (h2 : Odd a2) (h3 : Odd a3)
    (h4 : Odd a4) (h5 : Odd a5) (h6 : Odd a6) (h7 : Odd a7)
    (h8 : Odd a8) :
    Odd (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8) := by
  have h01 := h0.add_odd h1
  have h012 := h01.add_odd h2
  have h0123 := h012.add_odd h3
  have h01234 := h0123.add_odd h4
  have h012345 := h01234.add_odd h5
  have h0123456 := h012345.add_odd h6
  have h01234567 := h0123456.add_odd h7
  exact h01234567.add_odd h8

theorem even_sum_twelve
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Int}
    (h0 : Odd a0) (h1 : Odd a1) (h2 : Odd a2) (h3 : Odd a3)
    (h4 : Odd a4) (h5 : Odd a5) (h6 : Odd a6) (h7 : Odd a7)
    (h8 : Odd a8) (h9 : Odd a9) (h10 : Odd a10) (h11 : Odd a11) :
    Even (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 +
      a10 + a11) := by
  have h01 := h0.add_odd h1
  have h012 := h01.add_odd h2
  have h0123 := h012.add_odd h3
  have h01234 := h0123.add_odd h4
  have h012345 := h01234.add_odd h5
  have h0123456 := h012345.add_odd h6
  have h01234567 := h0123456.add_odd h7
  have h012345678 := h01234567.add_odd h8
  have h0123456789 := h012345678.add_odd h9
  have h012345678910 := h0123456789.add_odd h10
  exact h012345678910.add_odd h11

theorem layerInternalInt_even (s : Nat) :
    Even (layerInternalInt s) := by
  unfold layerInternalInt
  apply even_sum_twelve <;> exact (spinCode_odd _ _).mul (spinCode_odd _ _)

theorem layerLateralInt_even (s : Nat) :
    Even (layerLateralInt s) := by
  unfold layerLateralInt
  exact ((((((((layerInternalInt_even s).add (even_two_mul _)).add_odd
    (spinCode_odd _ _)).add_even (even_two_mul _)).add_odd
    (spinCode_odd _ _)).add_odd (spinCode_odd _ _)).add_even
    (even_two_mul _)).add_odd (spinCode_odd _ _)).add (even_two_mul _)

theorem layerFaceInt_odd (s : Nat) : Odd (layerFaceInt s) := by
  unfold layerFaceInt
  exact odd_sum_nine (spinCode_odd _ _) (spinCode_odd _ _)
    (spinCode_odd _ _) (spinCode_odd _ _) (spinCode_odd _ _)
    (spinCode_odd _ _) (spinCode_odd _ _) (spinCode_odd _ _)
    (spinCode_odd _ _)

theorem layerDotInt_odd (s t : Nat) : Odd (layerDotInt s t) := by
  unfold layerDotInt
  apply odd_sum_nine <;> exact (spinCode_odd _ _).mul (spinCode_odd _ _)

theorem layerLateralInt_halfShift (s : Fin 512) :
    2 * halfShift (layerLateralInt s) 16 = layerLateralInt s + 16 := by
  unfold halfShift
  exact Int.two_mul_ediv_two_of_even ((layerLateralInt_even s).add (by norm_num))

theorem layerEndpointInt_halfShift (q : Fin 512) :
    2 * halfShift (layerLateralInt q + layerFaceInt q) 17 =
      layerLateralInt q + layerFaceInt q + 17 := by
  unfold halfShift
  exact Int.two_mul_ediv_two_of_even
    ((layerLateralInt_even q).add_odd (layerFaceInt_odd q) |>.add_odd (by norm_num))

theorem layerSeamInt_halfShift (s q : Fin 512) :
    2 * halfShift (layerDotInt s q) 9 = layerDotInt s q + 9 := by
  unfold halfShift
  exact Int.two_mul_ediv_two_of_even
    ((layerDotInt_odd s q).add_odd (by norm_num))

theorem layerMiddleInt_halfShift (s v : Fin 512) :
    2 * halfShift
        (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26 =
      layerDotInt s v + layerLateralInt v + layerFaceInt v + 26 := by
  unfold halfShift
  exact Int.two_mul_ediv_two_of_even
    (((layerDotInt_odd s v).add_even (layerLateralInt_even v)).add_odd
      (layerFaceInt_odd v) |>.add (by norm_num))

theorem eval_rawMomentDirectBlock (X Y : Real)
    (start count : Nat) :
    (rawMomentDirectBlock start count).eval X Y =
      ((List.range count).map fun offset =>
        (rawMomentStatePoly (start + offset)).eval X Y).sum := by
  unfold rawMomentDirectBlock
  rw [eval_foldl_add_apply]
  simp

theorem list_range_mul_sum_blocks (f : Nat -> Real)
    (blocks width : Nat) :
    ((List.range (blocks * width)).map f).sum =
      ((List.range blocks).map fun block =>
        ((List.range width).map fun offset =>
          f (block * width + offset)).sum).sum := by
  induction blocks with
  | zero => simp
  | succ blocks ih =>
      rw [Nat.succ_mul, List.range_add, List.map_append,
        List.sum_append, ih]
      simp [List.range_succ, Function.comp_def]

theorem eval_rawMomentPolyStateSum_eq_fin_sum (X Y : Real) :
    rawMomentPolyStateSum.eval X Y =
      ∑ s : Fin 512, (rawMomentStatePoly s).eval X Y := by
  calc
    rawMomentPolyStateSum.eval X Y =
        ((List.range 256).map fun block =>
          (rawMomentDirectBlock (2 * block) 2).eval X Y).sum := by
      unfold rawMomentPolyStateSum
      rw [eval_foldl_add_apply]
      simp
    _ = ((List.range 256).map fun block =>
          ((List.range 2).map fun offset =>
            (rawMomentStatePoly (block * 2 + offset)).eval X Y).sum).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro block hblock
      rw [eval_rawMomentDirectBlock]
      simp only [Nat.mul_comm]
    _ = ((List.range (256 * 2)).map fun s =>
          (rawMomentStatePoly s).eval X Y).sum := by
      rw [list_range_mul_sum_blocks]
    _ = ∑ s : Fin 512, (rawMomentStatePoly s).eval X Y := by
      norm_num
      rw [list_range_sum_eq_finset_range_sum]
      exact (Fin.sum_univ_eq_sum_range
        (fun s : Nat => (rawMomentStatePoly s).eval X Y) 512).symm

set_option maxRecDepth 10000 in


theorem eval_rawMomentPolyStateSum (X Y : Real)
    (hX : X ≠ 0) (hY : Y ≠ 0) :
    rawMomentPolyStateSum.eval X Y =
      ∑ s : Fin 512,
        X ^ halfShift (layerLateralInt s) 16 *
          (∑ v : Fin 512,
            X ^ halfShift
              (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26) *
          (∑ q : Fin 512,
            X ^ halfShift (layerLateralInt q + layerFaceInt q) 17 *
              Y ^ halfShift (layerDotInt s q) 9) := by
  rw [eval_rawMomentPolyStateSum_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold rawMomentStatePoly
  rw [BiPoly.eval_mul X Y hX hY, BiPoly.eval_mul X Y hX hY,
    BiPoly.eval_monomial, BiPoly.eval_sumCodes_eq_fin_sum,
    BiPoly.eval_sumCodes_eq_fin_sum]
  simp only [BiPoly.eval_monomial, Int.cast_one, one_mul, zpow_zero,
    mul_one]

theorem real_exp_zpow (x : Real) (z : Int) :
    Real.exp x ^ z = Real.exp ((z : Real) * x) := by
  cases z with
  | ofNat n =>
      change Real.exp x ^ (n : Int) = Real.exp ((n : Real) * x)
      rw [zpow_natCast, ← Real.exp_nat_mul]
  | negSucc n =>
      rw [zpow_negSucc, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      push_cast
      ring

end StatMech.FrontierA.NOneSymmetricMeanCertificate
