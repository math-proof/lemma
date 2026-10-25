/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreSandwichProof.Part6
import Def.StatisticalMechanics.Code.FK.RotationInvariance.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.show false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem rot_lift_edgeIncl (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N)) :
    edgeIncl d N (Sym2.map (S.lift N) eb) = Sym2.map S.τ (edgeIncl d N eb) := by
  unfold edgeIncl
  rw [Sym2.map_map, Sym2.map_map]
  apply Sym2.map_congr
  intro z _
  exact BoxSym.lift_val S N z


theorem rot_site_mem_box (x : Site d) :
    x ∈ box d (Finset.univ.sup (fun i => (x i).natAbs)) :=
  fun i => Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)


theorem rot_free_density_boxSym (S : BoxSym d) (e : Sym2 (Site d))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (Sym2.map S.τ e) p = freeEdgeDensity d 2 e p := by
  induction e with
  | h x y =>
    obtain ⟨N, hxN, hyN⟩ : ∃ N, x ∈ box d N ∧ y ∈ box d N :=
      ⟨max (Finset.univ.sup (fun i => (x i).natAbs))
            (Finset.univ.sup (fun i => (y i).natAbs)),
        fun i => le_trans (rot_site_mem_box x i) (Nat.le_max_left _ _),
        fun i => le_trans (rot_site_mem_box y i) (Nat.le_max_right _ _)⟩
    set eb : Sym2 (boxVerts d N) := s((⟨x, hxN⟩ : boxVerts d N), (⟨y, hyN⟩ : boxVerts d N)) with heb
    have hincl : edgeIncl d N eb = s(x, y) := by
      unfold edgeIncl; rw [heb, Sym2.map_mk]
    rw [← hincl, ← rot_lift_edgeIncl S N eb]
    exact (fkTI_free_density_shift_inv S N eb hp hp1).symm


theorem rot_wired_density_boxSym (S : BoxSym d) (e : Sym2 (Site d))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (Sym2.map S.τ e) p = wiredEdgeDensity d 2 e p := by
  induction e with
  | h x y =>
    obtain ⟨N, hxN, hyN⟩ : ∃ N, x ∈ box d N ∧ y ∈ box d N :=
      ⟨max (Finset.univ.sup (fun i => (x i).natAbs))
            (Finset.univ.sup (fun i => (y i).natAbs)),
        fun i => le_trans (rot_site_mem_box x i) (Nat.le_max_left _ _),
        fun i => le_trans (rot_site_mem_box y i) (Nat.le_max_right _ _)⟩
    set eb : Sym2 (boxVerts d N) := s((⟨x, hxN⟩ : boxVerts d N), (⟨y, hyN⟩ : boxVerts d N)) with heb
    have hincl : edgeIncl d N eb = s(x, y) := by
      unfold edgeIncl; rw [heb, Sym2.map_mk]
    rw [← hincl, ← rot_lift_edgeIncl S N eb]
    exact (fkTI_wired_density_shift_inv S N eb hp hp1).symm


theorem rot_free_density_recentre (x y : Site d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p
      = freeEdgeDensity d 2 (s((0 : Site d), y - x) : Sym2 (Site d)) p := by
  rw [bdp_freeEdgeDensity_translation_inv hp hp1 (Multiplicative.ofAdd x) (s(x, y))]
  congr 1
  show s((Multiplicative.ofAdd x)⁻¹ • x, (Multiplicative.ofAdd x)⁻¹ • y) = s((0 : Site d), y - x)
  have h1 : (Multiplicative.ofAdd x)⁻¹ • x = (0 : Site d) := by
    show -x + x = 0; rw [neg_add_cancel]
  have h2 : (Multiplicative.ofAdd x)⁻¹ • y = y - x := by
    show -x + y = y - x; abel
  rw [h1, h2]


theorem rot_wired_density_recentre (x y : Site d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p
      = wiredEdgeDensity d 2 (s((0 : Site d), y - x) : Sym2 (Site d)) p := by
  rw [bdp_wiredEdgeDensity_translation_inv hp hp1 (Multiplicative.ofAdd x) (s(x, y))]
  congr 1
  show s((Multiplicative.ofAdd x)⁻¹ • x, (Multiplicative.ofAdd x)⁻¹ • y) = s((0 : Site d), y - x)
  have h1 : (Multiplicative.ofAdd x)⁻¹ • x = (0 : Site d) := by
    show -x + x = 0; rw [neg_add_cancel]
  have h2 : (Multiplicative.ofAdd x)⁻¹ • y = y - x := by
    show -x + y = y - x; abel
  rw [h1, h2]


theorem rot_candMap_apply (j : Fin d) (b : Bool) (i : Fin d) :
    candMap d (0 : Site d) (j, b) i = (if i = j then (if b then 1 else -1) else 0) := by
  show Function.update (0 : Site d) j ((0 : Site d) j + (if b then 1 else -1)) i = _
  by_cases h : i = j
  · subst h; rw [Function.update_self]; simp
  · rw [Function.update_of_ne h]; simp [h]


theorem rot_boxSym_fixes_zero (S : BoxSym d) : S.τ (0 : Site d) = 0 := by
  
  have h0 : S.τ (0 : Site d) ∈ box d 0 := (S.box_mem 0 0).mpr (fun i => by simp)
  funext i
  have hi : (S.τ (0 : Site d) i).natAbs ≤ 0 := h0 i
  have : (S.τ (0 : Site d) i).natAbs = 0 := Nat.le_zero.mp hi
  simpa using Int.natAbs_eq_zero.mp this


theorem rot_signFlip_neg_to_pos (j : Fin d) :
    (fkTI_signFlip d j).τ (candMap d (0 : Site d) (j, false)) = candMap d (0 : Site d) (j, true) := by
  funext i
  show (if i = j then -(candMap d (0 : Site d) (j, false) i) else candMap d (0 : Site d) (j, false) i)
      = candMap d (0 : Site d) (j, true) i
  rw [rot_candMap_apply, rot_candMap_apply]
  by_cases h : i = j <;> simp [h]


theorem rot_permEquiv_axis_to_zero (j : Fin d) (hd : 0 < d) :
    rot_permEquiv d (Equiv.swap (⟨0, hd⟩ : Fin d) j) (candMap d (0 : Site d) (j, true))
      = candMap d (0 : Site d) (⟨0, hd⟩, true) := by
  funext i
  show (candMap d (0 : Site d) (j, true)) ((Equiv.swap (⟨0, hd⟩ : Fin d) j).symm i)
      = candMap d (0 : Site d) (⟨0, hd⟩, true) i
  rw [rot_candMap_apply, rot_candMap_apply, Equiv.symm_swap]
  have hiff : ((Equiv.swap (⟨0, hd⟩ : Fin d) j) i = j) ↔ (i = ⟨0, hd⟩) := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  by_cases h : (Equiv.swap (⟨0, hd⟩ : Fin d) j) i = j
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]


end FK
end StatMech
