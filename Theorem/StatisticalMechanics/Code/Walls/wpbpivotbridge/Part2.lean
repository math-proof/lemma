/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wcddefectbridge.Part5
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
import Def.StatisticalMechanics.Code.Walls.wpbpivotbridge
open scoped BigOperators
open Finset
open SimpleGraph Function


namespace StatMech

namespace Wpb

open StatMech.Lattice

open StatMech.Wad

open StatMech.Wcd

open StatMech.Walls

open StatMech.Euc


theorem wpb_pivotInjective (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hpf : WpbPinchFree K a) :
    Set.InjOn (fun i => wcd_pivot ((dartNext K)^[i] a.1)) (Set.Iio (dartOrbitPeriod K a)) := by
  intro i hi j hj hij
  have hii : i < dartOrbitPeriod K a := Set.mem_Iio.mp hi
  have hjj : j < dartOrbitPeriod K a := Set.mem_Iio.mp hj
  have hbi := iterate_isBoundaryDart K a.1 a.2 i
  have hbj := iterate_isBoundaryDart K a.1 a.2 j
  have hde : (dartNext K)^[i] a.1 = (dartNext K)^[j] a.1 :=
    wpb_pivot_inj_nonpinch K hbi hbj (hpf i hii) hij
  have hsub : (dartNextSub K)^[i] a = (dartNextSub K)^[j] a := by
    apply Subtype.ext
    rw [dartNextSub_iterate_val, dartNextSub_iterate_val]; exact hde
  exact jc5_orbit_injOn_Iio K a hi hj hsub


theorem wpb_unitWt_e1 : unitWt (![1, 0] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]

theorem wpb_unitWt_me1 : unitWt (![-1, 0] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]

theorem wpb_unitWt_e2 : unitWt (![0, 1] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]

theorem wpb_unitWt_me2 : unitWt (![0, -1] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]


theorem wpb_defect_zero_of_no_boundary_pivot (K : Set (Site 2)) (hK : K.Finite)
    (x y : ℤ) (hv : ((x, y) : ℤ × ℤ) ∈ regVerts (wcd_toVtxFinset K hK))
    (hnp : ∀ e : Dart, IsBoundaryDart K e → wcd_pivot e ≠ (x, y)) :
    defect (wcd_toVtxFinset K hK) (x, y) = 0 := by
  classical
  set K' := wcd_toVtxFinset K hK with hK'
  have siteEq : ∀ p q : Site 2, p 0 = q 0 → p 1 = q 1 → p = q := by
    intro p q h0 h1; funext i; fin_cases i; exacts [h0, h1]
  
  have hmem : ∀ a b : ℤ, (![a, b] : Site 2) ∈ K ↔ ((a, b) : ℤ × ℤ) ∈ K' := by
    intro a b
    have h := (wcd_siteToVtx_mem_toVtxFinset K hK (![a, b] : Site 2)).symm
    rw [hK']
    simpa only [wcd_siteToVtx_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using h
  
  have notbd : ∀ (p g : Site 2) (h : unitWt g = 1),
      wcd_pivot (mkDart p g h) = (x, y) → ¬ ((p ∈ K) ∧ ((p + g) ∉ K)) := by
    intro p g h hpiv hbd
    exact hnp (mkDart p g h) hbd hpiv
  
  have impl : ∀ (ax ay bx byy : ℤ) (g : Site 2) (h : unitWt g = 1),
      ((![ax, ay] : Site 2) + g = ![bx, byy]) →
      wcd_pivot (mkDart ![ax, ay] g h) = (x, y) →
      ((ax, ay) ∈ K' → (bx, byy) ∈ K') := by
    intro ax ay bx byy g h hgadd hpiv hin
    by_contra hout
    exact notbd ![ax, ay] g h hpiv ⟨(hmem ax ay).mpr hin,
      by rw [hgadd]; exact fun hc => hout ((hmem bx byy).mp hc)⟩
  
  have hp1 : wcd_pivot (mkDart ![x-1, y] ![1, 0] wpb_unitWt_e1) = (x, y) := by
    refine Prod.ext ?_ ?_ <;>
      simp only [wcd_pivot, wcd_pivotSite, wcd_posPartSite, wcd_siteToVtx_apply, mkDart_tail,
        mkDart_dir, Pi.add_apply, Pi.neg_apply, rot90Fun_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_neg, neg_zero] <;> omega
  have hp2 : wcd_pivot (mkDart ![x, y-1] ![-1, 0] wpb_unitWt_me1) = (x, y) := by
    refine Prod.ext ?_ ?_ <;>
      simp only [wcd_pivot, wcd_pivotSite, wcd_posPartSite, wcd_siteToVtx_apply, mkDart_tail,
        mkDart_dir, Pi.add_apply, Pi.neg_apply, rot90Fun_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_neg, neg_zero] <;> omega
  have hp3 : wcd_pivot (mkDart ![x-1, y-1] ![0, 1] wpb_unitWt_e2) = (x, y) := by
    refine Prod.ext ?_ ?_ <;>
      simp only [wcd_pivot, wcd_pivotSite, wcd_posPartSite, wcd_siteToVtx_apply, mkDart_tail,
        mkDart_dir, Pi.add_apply, Pi.neg_apply, rot90Fun_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_neg, neg_zero] <;> omega
  have hp4 : wcd_pivot (mkDart ![x, y] ![0, -1] wpb_unitWt_me2) = (x, y) := by
    refine Prod.ext ?_ ?_ <;>
      simp only [wcd_pivot, wcd_pivotSite, wcd_posPartSite, wcd_siteToVtx_apply, mkDart_tail,
        mkDart_dir, Pi.add_apply, Pi.neg_apply, rot90Fun_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_neg, neg_zero] <;> omega
  
  have ha1 : (![x-1, y] : Site 2) + ![1, 0] = ![x, y] := by
    refine siteEq _ _ ?_ ?_ <;>
      simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] <;> omega
  have ha2 : (![x, y-1] : Site 2) + ![-1, 0] = ![x-1, y-1] := by
    refine siteEq _ _ ?_ ?_ <;>
      simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] <;> omega
  have ha3 : (![x-1, y-1] : Site 2) + ![0, 1] = ![x-1, y] := by
    refine siteEq _ _ ?_ ?_ <;>
      simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] <;> omega
  have ha4 : (![x, y] : Site 2) + ![0, -1] = ![x, y-1] := by
    refine siteEq _ _ ?_ ?_ <;>
      simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] <;> omega
  
  have i1 : ((x-1, y) ∈ K') → ((x, y) ∈ K') := impl (x-1) y x y ![1, 0] wpb_unitWt_e1 ha1 hp1
  have i2 : ((x, y-1) ∈ K') → ((x-1, y-1) ∈ K') :=
    impl x (y-1) (x-1) (y-1) ![-1, 0] wpb_unitWt_me1 ha2 hp2
  have i3 : ((x-1, y-1) ∈ K') → ((x-1, y) ∈ K') :=
    impl (x-1) (y-1) (x-1) y ![0, 1] wpb_unitWt_e2 ha3 hp3
  have i4 : ((x, y) ∈ K') → ((x, y-1) ∈ K') := impl x y x (y-1) ![0, -1] wpb_unitWt_me2 ha4 hp4
  
  have hdisj : (x-1, y-1) ∈ K' ∨ (x, y-1) ∈ K' ∨ (x-1, y) ∈ K' ∨ (x, y) ∈ K' := by
    rw [regVerts, Finset.mem_biUnion] at hv
    obtain ⟨c, hcK, hcv⟩ := hv
    rw [← wad_mem_surround_iff] at hcv
    unfold surroundCells at hcv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcv
    rcases hcv with rfl | rfl | rfl | rfl
    · exact Or.inl hcK
    · exact Or.inr (Or.inl hcK)
    · exact Or.inr (Or.inr (Or.inl hcK))
    · exact Or.inr (Or.inr (Or.inr hcK))
  
  have hall : (x-1, y-1) ∈ K' ∧ (x, y-1) ∈ K' ∧ (x-1, y) ∈ K' ∧ (x, y) ∈ K' := by
    tauto
  obtain ⟨hSW, hSE, hNW, hNE⟩ := hall
  
  have hcard4 : (surroundCells (x, y)).card = 4 := by
    simp only [surroundCells]
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton, Prod.mk.injEq]; omega),
        Finset.card_singleton]
  have hsub : surroundCells (x, y) ⊆ K' := by
    intro c hc
    unfold surroundCells at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> assumption
  have hcd : cellDeg K' (x, y) = 4 := by
    unfold cellDeg
    rw [Finset.inter_eq_left.mpr hsub, hcard4]
  
  have hed : (edgeDeg K' (x, y) : ℤ) = 4 := by
    rw [wcd_edgeDeg_formula K' x y]
    simp only [hSW, hSE, hNW, hNE, or_true, true_or, if_true]
    norm_num
  
  have hdef : (defect K' (x, y) : ℤ) = 4 - 2 * (edgeDeg K' (x, y) : ℤ) + (cellDeg K' (x, y) : ℤ) :=
    rfl
  rw [hdef, hed, hcd]; norm_num


end Wpb
end StatMech
