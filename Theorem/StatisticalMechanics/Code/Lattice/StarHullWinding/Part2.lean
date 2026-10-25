/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Theorem.StatisticalMechanics.Code.Lattice.WindingEarInduction.Part3
import Def.StatisticalMechanics.Code.Lattice.StarHullWinding
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem shw_windingWitness_of_minLeft (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hcyc : (mpl_orbitLoop K a).IsCycle) (hres : shw_MinVertStepLeft K a) :
    wei_WindingWitness K a := by
  classical
  obtain ⟨k, hk, hvk, hkmin, hdir⟩ := hres
  set e := (dartNext K)^[k] a.1 with he_def
  have hbe : IsBoundaryDart K e := iterate_isBoundaryDart K a.1 a.2 k
  
  set c : ℤ := dartFace e 0 with hc
  set r : ℤ := dartFace e 1 with hr
  
  have hlow : dartFace e = (![c, r] : Site 2) := by
    funext i; fin_cases i <;> rfl
  
  have hc' : c = e.tail 0 - 1 := by rw [hc, dartFace_of_dir_left e hdir]; simp
  have hr' : r = e.tail 1 - 1 := by rw [hr, dartFace_of_dir_left e hdir]; simp
  have hup : dartFace (dartNext K e) = (![c, r + 1] : Site 2) := by
    rw [dartFace_next_of_dir_left K e hdir]
    funext i; fin_cases i
    · change e.tail 0 - 1 = c; omega
    · change e.tail 1 = r + 1; omega
  
  have hsucc : (dartNext K)^[k + 1] a.1 = dartNext K e := by
    rw [he_def, Function.iterate_succ_apply']
  
  have he0 : s((![c, r] : Site 2), ![c, r + 1]) ∈ (mpl_orbitLoop K a).edges := by
    rw [shw_mpl_edges_form, List.mem_map]
    refine ⟨k, List.mem_range.mpr hk, ?_⟩
    rw [show (dartNext K)^[k] a.1 = e from rfl, ← hlow, hsucc, hup]
  
  have hmin : ∀ x y : Site 2, s(x, y) ∈ (mpl_orbitLoop K a).edges → x 0 = y 0 → c ≤ x 0 := by
    intro x y hxy hcol
    apply shw_minCol_le_of_vertEdge K a c ?_ hxy hcol
    intro j hj hvj
    exact hkmin j hj hvj
  
  have hnodup : (mpl_orbitLoop K a).edges.Nodup := hcyc.edges_nodup
  have hone : jec_rayCount (![c + 1, r + 1] : Site 2) (mpl_orbitLoop K a) = 1 :=
    eaw_rayCount_extreme (mpl_orbitLoop K a) c r hmin he0 hnodup
  
  have hzmem : (![c + 1, r + 1] : Site 2) ∈ K := by
    have := shw_extremeCell_mem_of_left hbe hdir
    rwa [← hc, ← hr] at this
  exact ⟨![c + 1, r + 1], hzmem, by rw [hone]; decide⟩


theorem shw_starHull_mpl_isCycle (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a) :
    (mpl_orbitLoop (ndt_StarHull K) a).IsCycle :=
  mpl_orbitLoop_isCycle (ndt_StarHull K) a hp
    (orbitFace_injOn_of_noPinch (ndt_StarHull K) a (ndt_orbitFaceNoPinch K a))


theorem shw_starHull_windingWitness_of_minLeft (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a)
    (hres : shw_MinVertStepLeft (ndt_StarHull K) a) :
    wei_WindingWitness (ndt_StarHull K) a :=
  shw_windingWitness_of_minLeft (ndt_StarHull K) a (shw_starHull_mpl_isCycle K a hp) hres


theorem shw_unitCell_faceInj :
    Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucBase.1))
      (Set.Iio (dartOrbitPeriod unitCell ucBase)) := by
  rw [unitCell_orbitPeriod_eq_four, show ucBase.1 = ucDart0 from rfl]
  exact unitCell_orbitFace_injOn


theorem shw_unitCell_minVertStepLeft : shw_MinVertStepLeft unitCell ucBase := by
  refine ⟨2, ?_, ?_, ?_, ?_⟩
  · rw [unitCell_orbitPeriod_eq_four]; norm_num
  · 
    rw [show ucBase.1 = ucDart0 from rfl, mpl_dartFace_iterate_ucDart2,
        mpl_dartFace_iterate_ucDart3]
    rfl
  · 
    intro j hj hvj
    rw [show ucBase.1 = ucDart0 from rfl, mpl_dartFace_iterate_ucDart2]
    change (-1 : ℤ) ≤ (dartFace ((dartNext unitCell)^[j] ucDart0)) 0
    rw [unitCell_orbitPeriod_eq_four] at hj
    interval_cases j
    · rw [mpl_dartFace_iterate_ucDart0]; norm_num
    · rw [mpl_dartFace_iterate_ucDart1]; norm_num
    · rw [mpl_dartFace_iterate_ucDart2]; norm_num
    · rw [mpl_dartFace_iterate_ucDart3]; norm_num
  · 
    rw [show ucBase.1 = ucDart0 from rfl, iterate_ucDart_2, ucDart2_dir]


theorem shw_unitCell_windingWitness : wei_WindingWitness unitCell ucBase := by
  have hcyc : (mpl_orbitLoop unitCell ucBase).IsCycle :=
    mpl_orbitLoop_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
      shw_unitCell_faceInj
  exact shw_windingWitness_of_minLeft unitCell ucBase hcyc shw_unitCell_minVertStepLeft


theorem shw_kingSat_excludes_diagSubcase {K : Set (Site 2)} (hK : npd_NoDiagTouch K)
    {e : Dart} (he : IsBoundaryDart K e) (hd : e.dir = ![1, 0]) (c r : ℤ)
    (hc : c = dartFace e 0) (hr : r + 1 = dartFace e 1) :
    ¬ ((![c + 1, r] : Site 2) ∈ K ∧ (![c, r] : Site 2) ∉ K) := by
  rintro ⟨hP10, hP00⟩
  obtain ⟨hcP00, hcP10⟩ := npd_corners_right he hd
  
  
  
  apply hK (![c, r] : Site 2)
  right
  refine ⟨?_, ?_, hP00, ?_⟩
  · 
    change (npd_P10 (![c, r] : Site 2)) ∈ K
    have : (npd_P10 (![c, r] : Site 2)) = ![c + 1, r] := by
      unfold npd_P10; funext i; fin_cases i <;> simp
    rw [this]; exact hP10
  · 
    change (![c, r + 1] : Site 2) ∈ K
    have : (npd_P00 (dartFace e) : Site 2) = ![c, r + 1] := by
      unfold npd_P00; funext i; fin_cases i
      · change dartFace e 0 = c; omega
      · change dartFace e 1 = r + 1; omega
    rwa [this] at hcP00
  · 
    change (![c + 1, r + 1] : Site 2) ∉ K
    have : (npd_P10 (dartFace e) : Site 2) = ![c + 1, r + 1] := by
      unfold npd_P10; funext i; fin_cases i
      · change dartFace e 0 + 1 = c + 1; omega
      · change dartFace e 1 = r + 1; omega
    rwa [this] at hcP10

end Lattice
end StatMech
