/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamHeadlineAdapter
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGraphAdapter
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedVBGTriangle
import Def.StatisticalMechanics.Code.FrontierA.GrahamPinnedFieldAdapter.Part3
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.ConfigSpace

open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


@[simp] theorem grahamAnchorSlice_at (m : V) (b : Bool)
    (eta : {x : V // x ≠ m} -> Bool) :
    grahamAnchorSlice m b eta m = b := by
  simp [grahamAnchorSlice, Equiv.funSplitAt, Equiv.piSplitAt]

@[simp] theorem grahamAnchorSlice_ne (m : V) (b : Bool)
    (eta : {x : V // x ≠ m} -> Bool) (x : {x : V // x ≠ m}) :
    grahamAnchorSlice m b eta x.1 = eta x := by
  simp [grahamAnchorSlice, Equiv.funSplitAt, Equiv.piSplitAt, x.2]

theorem grahamPinConfig_anchorSlice (m : V) (b : Bool)
    (eta : {x : V // x ≠ m} -> Bool) :
    grahamPinConfig m (grahamAnchorSlice m b eta) =
      grahamAnchorSlice m true eta := by
  funext x
  by_cases hxm : x = m
  · subst x
    simp
  · let y : {x : V // x ≠ m} := ⟨x, hxm⟩
    rw [grahamPinConfig_of_ne m _ hxm]
    exact (grahamAnchorSlice_ne m b eta y).trans
      (grahamAnchorSlice_ne m true eta y).symm


theorem grahamAnchor_sum_eq_two_mul_trueSlice
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (m : V)
    (F : ConfigSpace V -> Real)
    (hF : ∀ t, F (grahamPinConfig m t) = F t) :
    (∑ t : ConfigSpace V,
        F t * wJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) t) =
      2 * ∑ eta : {x : V // x ≠ m} -> Bool,
        F (grahamAnchorSlice m true eta) *
          wJ E J (fun _ => 0) (grahamAnchorSlice m true eta) := by
  rw [← Equiv.sum_comp (Equiv.funSplitAt m Bool).symm]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have hslice (b : Bool) (eta : {x : V // x ≠ m} -> Bool) :
      F (grahamAnchorSlice m b eta) *
          wJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m)
            (grahamAnchorSlice m b eta) =
        F (grahamAnchorSlice m true eta) *
          wJ E J (fun _ => 0) (grahamAnchorSlice m true eta) := by
    rw [← hF (grahamAnchorSlice m b eta),
      grahamAnchor_weight_eq_pin E J hdiag,
      grahamPinConfig_anchorSlice]
  simp only [grahamAnchorSlice] at hslice ⊢
  simp_rw [hslice]
  ring


theorem graham_trueSlice_sum_eq_half_Z
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V) :
    (∑ eta : {x : V // x ≠ m} -> Bool,
        wJ E J (fun _ => 0) (grahamAnchorSlice m true eta)) =
      ZJ E J (fun _ => 0) / 2 := by
  have hhalf := vbg_exp_grahamZeroProb_coordUp E J m
  have hslice :
      (∑ s : ConfigSpace V,
          wJ E J (fun _ => 0) s * vbg_coordUp m s) =
        ∑ eta : {x : V // x ≠ m} -> Bool,
          wJ E J (fun _ => 0) (grahamAnchorSlice m true eta) := by
    rw [← Equiv.sum_comp (Equiv.funSplitAt m Bool).symm]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [grahamAnchorSlice]
    simp [vbg_coordUp, Equiv.funSplitAt, Equiv.piSplitAt]
  unfold vbg_exp grahamZeroProb at hhalf
  rw [show (∑ s : ConfigSpace V,
      wJ E J (fun _ => 0) s / ZJ E J (fun _ => 0) * vbg_coordUp m s) =
      (∑ s : ConfigSpace V,
        wJ E J (fun _ => 0) s * vbg_coordUp m s) /
          ZJ E J (fun _ => 0) by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      ring,
    hslice] at hhalf
  have hZ : ZJ E J (fun _ => 0) ≠ 0 := (ZJ_pos E J (fun _ => 0)).ne'
  field_simp [hZ] at hhalf ⊢
  linarith


theorem grahamAnchor_ZJ_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (m : V) :
    ZJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) =
      ZJ E J (fun _ => 0) := by
  unfold ZJ
  have hsum := grahamAnchor_sum_eq_two_mul_trueSlice E J hdiag m
    (fun _ => (1 : Real)) (by intro t; rfl)
  simp only [one_mul] at hsum
  rw [hsum, graham_trueSlice_sum_eq_half_Z]
  simp [ZJ]
  ring


theorem vbg_exp_grahamPinnedProb_eq_trueSlice
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V)
    (F : ConfigSpace V -> Real) :
    vbg_exp (grahamPinnedProb E J m) F =
      (2 * ∑ eta : {x : V // x ≠ m} -> Bool,
        F (grahamAnchorSlice m true eta) *
          wJ E J (fun _ => 0) (grahamAnchorSlice m true eta)) /
        ZJ E J (fun _ => 0) := by
  rw [vbg_exp_grahamPinnedProb_eq,
    grahamZeroProb_coordUp_eq_half]
  have hslice :
      (∑ s : ConfigSpace V,
          wJ E J (fun _ => 0) s * (vbg_coordUp m s * F s)) =
        ∑ eta : {x : V // x ≠ m} -> Bool,
          F (grahamAnchorSlice m true eta) *
            wJ E J (fun _ => 0) (grahamAnchorSlice m true eta) := by
    rw [← Equiv.sum_comp (Equiv.funSplitAt m Bool).symm]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [grahamAnchorSlice]
    simp [vbg_coordUp, Equiv.funSplitAt, Equiv.piSplitAt]
    apply Finset.sum_congr rfl
    intro eta _
    ring
  unfold vbg_exp grahamZeroProb
  rw [show (∑ s : ConfigSpace V,
      wJ E J (fun _ => 0) s / ZJ E J (fun _ => 0) *
        (vbg_coordUp m s * F s)) =
      (∑ s : ConfigSpace V,
        wJ E J (fun _ => 0) s * (vbg_coordUp m s * F s)) /
          ZJ E J (fun _ => 0) by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      ring,
    hslice]
  have hZ : ZJ E J (fun _ => 0) ≠ 0 := (ZJ_pos E J (fun _ => 0)).ne'
  field_simp [hZ]


theorem grahamAnchor_expJ_eq_pinned
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (m : V)
    (F : ConfigSpace V -> Real)
    (hF : ∀ t, F (grahamPinConfig m t) = F t) :
    expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) F =
      vbg_exp (grahamPinnedProb E J m) F := by
  unfold expJ
  rw [grahamAnchor_ZJ_eq E J hdiag m,
    grahamAnchor_sum_eq_two_mul_trueSlice E J hdiag m F hF,
    vbg_exp_grahamPinnedProb_eq_trueSlice]


theorem grahamAnchor_onePoint_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) {m x : V} (hxm : x ≠ m) :
    expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m)
        (fun t => spin t x) =
      grahamTwoPoint E J x m := by
  rw [grahamAnchor_expJ_eq_pinned E J hdiag m]
  · exact vbg_exp_grahamPinnedProb_spin E J m x
  · intro t
    rw [spin_grahamPinConfig_of_ne m t hxm]


theorem grahamAnchor_twoPoint_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) {m x y : V}
    (hxm : x ≠ m) (hym : y ≠ m) :
    expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m)
        (fun t => spin t x * spin t y) =
      grahamTwoPoint E J x y := by
  rw [grahamAnchor_expJ_eq_pinned E J hdiag m]
  · exact vbg_exp_grahamPinnedProb_twoSpin E J m x y
  · intro t
    rw [spin_grahamPinConfig_of_ne m t hxm,
      spin_grahamPinConfig_of_ne m t hym]


theorem vbg_exp_grahamPinnedProb_threeSpin
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m i j k : V) :
    vbg_exp (grahamPinnedProb E J m)
        (fun t => spin t i * (spin t j * spin t k)) =
      grahamFourPoint E J i j k m := by
  rw [vbg_exp_grahamPinnedProb E J m]
  have hzero := vbg_exp_grahamZeroProb_threeSpin_eq_zero E J i j k
  rw [show (fun t : ConfigSpace V => spin t i * (spin t j * spin t k)) =
      (fun t => spin t i * spin t j * spin t k) by
        funext t; ring,
    hzero, zero_add,
    vbg_exp_grahamZeroProb_eq_expJ,
    grahamFourPoint_eq_expJ]
  congr 1
  funext t
  ring


theorem grahamAnchor_threePoint_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) {m i j k : V}
    (him : i ≠ m) (hjm : j ≠ m) (hkm : k ≠ m) :
    expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m)
        (fun t => spin t i * (spin t j * spin t k)) =
      grahamFourPoint E J i j k m := by
  rw [grahamAnchor_expJ_eq_pinned E J hdiag m]
  · exact vbg_exp_grahamPinnedProb_threeSpin E J m i j k
  · intro t
    rw [spin_grahamPinConfig_of_ne m t him,
      spin_grahamPinConfig_of_ne m t hjm,
      spin_grahamPinConfig_of_ne m t hkm]

end StatMech.FrontierA
