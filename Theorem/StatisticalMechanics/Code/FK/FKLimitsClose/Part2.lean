/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Def.StatisticalMechanics.Code.FK.FKLimitsClose.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


@[simp] theorem flc_incl_val {Sin Sout : Set (Site d)} (hsub : Sin ⊆ Sout)
    (x : {y : Site d // y ∈ Sin}) : (flc_incl hsub x : Site d) = (x : Site d) := rfl

theorem flc_incl_injective {Sin Sout : Set (Site d)} (hsub : Sin ⊆ Sout) :
    Function.Injective (flc_incl hsub) := by
  intro x y h
  exact Subtype.ext (by have := congrArg Subtype.val h; simpa using this)


theorem flc_hbdryIn_box {a : ℕ} (ha : 1 ≤ a)
    (x : {y : Site d // y ∈ box d a}) (z : Site d)
    (hnn : NearestNeighbour d (x : Site d) z) (hz : z ∉ box d a) :
    boxBoundary d a x := by
  refine ⟨x.2, notMem_box_pred_of_adj_outer ha x.2 hnn hz⟩


theorem flc_hbdryIn_transBox {m : ℕ} (hm : 1 ≤ m) (v : Site d)
    (x : {y : Site d // y ∈ fvs_transBox d m v}) (z : Site d)
    (hnn : NearestNeighbour d (x : Site d) z) (hz : z ∉ fvs_transBox d m v) :
    fvs_transBoxBoundary d m v x := by
  
  have hxm : ((x : Site d) - v) ∈ box d m := x.2
  have hznot : (z - v) ∉ box d m := fun hzm => hz hzm
  have hnn' : NearestNeighbour d ((x : Site d) - v) (z - v) := by
    unfold NearestNeighbour at hnn ⊢
    rw [← hnn]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    simp [Pi.sub_apply]
  
  exact ⟨hxm, notMem_box_pred_of_adj_outer hm hxm hnn' hznot⟩


theorem flc_hmargin_box_in_transBox (v : Site d) {a m : ℕ}
    (hsub : box d a ⊆ fvs_transBox d m v) (hcm : a + flc_vrad v + 1 ≤ m)
    (x : {y : Site d // y ∈ box d a}) :
    ¬ fvs_transBoxBoundary d m v (flc_incl hsub x) := by
  intro hbd
  
  have hmem : ((x : Site d) - v) ∈ box d (m - 1) := by
    intro i
    have hxi : (x.val i).natAbs ≤ a := x.2 i
    have hvi : (v i).natAbs ≤ flc_vrad v := flc_vrad_le v i
    have hsubi : ((flc_incl hsub x : Site d) - v) i = x.val i - v i := by
      simp [Pi.sub_apply]
    calc (((x : Site d) - v) i).natAbs = (x.val i - v i).natAbs := by simp [Pi.sub_apply]
      _ ≤ (x.val i).natAbs + (v i).natAbs := Int.natAbs_sub_le _ _
      _ ≤ a + flc_vrad v := Nat.add_le_add hxi hvi
      _ ≤ m - 1 := by omega
  exact (hbd.2) (by
    
    have : ((flc_incl hsub x : Site d) - v) = ((x : Site d) - v) := by
      funext i; simp [Pi.sub_apply]
    rw [this]; exact hmem)


theorem flc_hmargin_transBox_in_box (v : Site d) {m : ℕ}
    (hsub : fvs_transBox d m v ⊆ box d (m + flc_vrad v + 1))
    (x : {y : Site d // y ∈ fvs_transBox d m v}) :
    ¬ boxBoundary d (m + flc_vrad v + 1) (flc_incl hsub x) := by
  intro hbd
  
  have hmem : (x : Site d) ∈ box d (m + flc_vrad v) :=
    flc_transBox_subset_box v m x.2
  refine (hbd.2) ?_
  have hpred : m + flc_vrad v + 1 - 1 = m + flc_vrad v := by omega
  rw [show (flc_incl hsub x : Site d) = (x : Site d) from rfl, hpred]
  exact hmem


theorem flc_sym2map_val_injective {S : Set (Site d)} :
    Function.Injective (Sym2.map (Subtype.val : {y : Site d // y ∈ S} → Site d)) :=
  Sym2.map.injective Subtype.val_injective


theorem flc_image_eq_of_val_image_eq {S : Set (Site d)}
    {F G : Finset (Sym2 {y : Site d // y ∈ S})}
    (h : F.image (Sym2.map (Subtype.val : {y : Site d // y ∈ S} → Site d))
       = G.image (Sym2.map (Subtype.val : {y : Site d // y ∈ S} → Site d))) :
    F = G :=
  Finset.image_injective flc_sym2map_val_injective h


theorem flc_valMap_ocd_innerEdge {Sin Sout : Set (Site d)} (hsub : Sin ⊆ Sout)
    (e : Sym2 {y : Site d // y ∈ Sin}) :
    Sym2.map (Subtype.val : {y : Site d // y ∈ Sout} → Site d)
        (ocd_innerEdge (flc_incl hsub) e)
      = Sym2.map (Subtype.val : {y : Site d // y ∈ Sin} → Site d) e := by
  unfold ocd_innerEdge
  rw [Sym2.map_map]
  rfl


theorem flc_valImage_ocd_innerEdge_image {Sin Sout : Set (Site d)} (hsub : Sin ⊆ Sout)
    (F : Finset (Sym2 {y : Site d // y ∈ Sin})) :
    (F.image (ocd_innerEdge (flc_incl hsub))).image
        (Sym2.map (Subtype.val : {y : Site d // y ∈ Sout} → Site d))
      = F.image (Sym2.map (Subtype.val : {y : Site d // y ∈ Sin} → Site d)) := by
  rw [Finset.image_image]
  refine Finset.image_congr (fun e _ => ?_)
  exact flc_valMap_ocd_innerEdge hsub e


end FK
end StatMech
