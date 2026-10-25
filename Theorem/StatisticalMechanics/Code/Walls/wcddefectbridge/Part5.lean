/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BalanceContraction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Def.StatisticalMechanics.Code.Walls.wcddefectbridge.Part5
open scoped BigOperators
open Finset
open SimpleGraph Function


namespace StatMech

namespace Wcd

open StatMech.Lattice

open StatMech.Wad

open StatMech.Euc


theorem wcd_cornerBalance_eq_neg_defectSum (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hbr : WcdPivotBridge K hK a) :
    cornerBalance K a
      = - ∑ v ∈ regVerts (wcd_toVtxFinset K hK), defect (wcd_toVtxFinset K hK) v := by
  obtain ⟨hpf, hinj, hcov⟩ := hbr
  rw [wcd_cornerBalance_eq_neg_pivotSum K hK a hpf,
    wcd_pivotSum_eq_regVertsSum K hK a hinj hcov]


theorem wcd_cornerBalance_eq_neg_four (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hbr : WcdPivotBridge K hK a)
    (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
    cornerBalance K a = -4 := by
  rw [wcd_cornerBalance_eq_neg_defectSum K hK a hbr, wad_defect_eq_four_chi,
    euc_chi_induction hbuild]
  norm_num


theorem wcd_revCount_eq_neg_one (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hbr : WcdPivotBridge K hK a)
    (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
    revCount K a = -1 := by
  have h := wcd_cornerBalance_eq_neg_four K hK a hbr hbuild
  have h2 := cornerBalance_eq_four_revCount K a
  rw [h] at h2
  omega


theorem wcd_revCount_pm_one (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hbr : WcdPivotBridge K hK a)
    (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  Or.inr (wcd_revCount_eq_neg_one K hK a hbr hbuild)


theorem wcd_balanceIsFour (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hbr : WcdPivotBridge K hK a)
    (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
    BalanceIsFour K a :=
  (balanceIsFour_iff_revCount_pm_one K a).mpr (wcd_revCount_pm_one K hK a hbr hbuild)


theorem wcd_unitCell_finite : unitCell.Finite := by
  unfold unitCell; exact Set.finite_singleton _


theorem wcd_toVtxFinset_unitCell (hfin : unitCell.Finite) :
    wcd_toVtxFinset unitCell hfin = {((0 : ℤ), (0 : ℤ))} := by
  ext p
  rw [wcd_mem_toVtxFinset]
  simp only [Finset.mem_singleton]
  constructor
  · intro h
    have : (![((0 : ℤ)), 0] : Site 2) = wcd_siteToVtx.symm p := by
      have hu : wcd_siteToVtx.symm p ∈ unitCell := h
      unfold unitCell at hu
      rw [Set.mem_singleton_iff] at hu
      exact hu.symm
    have h0 := congrFun this 0
    have h1 := congrFun this 1
    simp only [wcd_siteToVtx, Equiv.coe_fn_symm_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
    exact Prod.ext h0.symm h1.symm
  · rintro rfl
    show wcd_siteToVtx.symm ((0 : ℤ), (0 : ℤ)) ∈ unitCell
    unfold unitCell
    rw [Set.mem_singleton_iff]
    funext i; fin_cases i <;> rfl


theorem wcd_witness_unitCell :
    cornerBalance unitCell ucBase
      = - ∑ v ∈ regVerts (wcd_toVtxFinset unitCell wcd_unitCell_finite),
          defect (wcd_toVtxFinset unitCell wcd_unitCell_finite) v := by
  rw [unitCell_cornerBalance ucBase (Or.inl rfl), wad_defect_eq_four_chi,
    wcd_toVtxFinset_unitCell, euc_chi_singleton]
  norm_num


theorem wcd_witness_pinch :
    wad_n2d ({((0 : ℤ), (0 : ℤ)), (1, 1)} : Finset (ℤ × ℤ)) = 1 := by decide


theorem wcd_witness_unitSquare_defectSum :
    ∑ v ∈ regVerts ({((0 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)),
        defect ({((0 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)) v = 4 := by
  rw [wad_defect_eq_four_chi, euc_chi_singleton]; norm_num

end Wcd
end StatMech
