/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
import Theorem.StatisticalMechanics.Code.Lattice.StarHullWinding.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingEarInduction.Part3
import Def.StatisticalMechanics.Code.Lattice.LexMinOrientation.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem lmo_minVertStepLeft_of_reachesLeftmost (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (m : ℤ) (hm : ∀ w ∈ K, m ≤ w 0)
    (hreach : lmo_OrbitReachesLeftmost K a m) :
    shw_MinVertStepLeft K a := by
  classical
  obtain ⟨k0, hk0, hv0, hcol0⟩ := hreach
  set p := dartOrbitPeriod K a with hp
  
  set S := (Finset.range p).filter
    (fun k => (dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0)
    with hS
  have hSne : S.Nonempty :=
    ⟨k0, by rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨hk0, hv0⟩⟩
  
  obtain ⟨k, hkS, hkmin⟩ :=
    S.exists_min_image (fun k => (dartFace ((dartNext K)^[k] a.1)) 0) hSne
  rw [hS, Finset.mem_filter, Finset.mem_range] at hkS
  obtain ⟨hklt, hkv⟩ := hkS
  have hkmin' : ∀ j < p,
      (dartFace ((dartNext K)^[j] a.1)) 0 = (dartFace ((dartNext K)^[j + 1] a.1)) 0 →
        (dartFace ((dartNext K)^[k] a.1)) 0 ≤ (dartFace ((dartNext K)^[j] a.1)) 0 := by
    intro j hj hvj
    exact hkmin j (by rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hvj⟩)
  
  have hk0S : k0 ∈ S := by rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨hk0, hv0⟩
  have hcolk : (dartFace ((dartNext K)^[k] a.1)) 0 ≤ m - 1 :=
    le_trans (hkmin k0 hk0S) hcol0
  
  have hbk : IsBoundaryDart K ((dartNext K)^[k] a.1) := iterate_isBoundaryDart K a.1 a.2 k
  have hkv' : (dartFace ((dartNext K)^[k] a.1)) 0
      = (dartFace (dartNext K ((dartNext K)^[k] a.1))) 0 := by
    rwa [← Function.iterate_succ_apply' (dartNext K) k a.1]
  have hleft : ((dartNext K)^[k] a.1).dir = ![-1, 0] :=
    lmo_vertStep_left_of_minCol m hm hbk hkv' hcolk
  exact ⟨k, hklt, hkv, hkmin', hleft⟩


theorem lmo_windingWitness_of_reachesLeftmost (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (m : ℤ) (hm : ∀ w ∈ K, m ≤ w 0)
    (hcyc : (mpl_orbitLoop K a).IsCycle)
    (hreach : lmo_OrbitReachesLeftmost K a m) :
    wei_WindingWitness K a :=
  shw_windingWitness_of_minLeft K a hcyc
    (lmo_minVertStepLeft_of_reachesLeftmost K a m hm hreach)


theorem lmo_unitCell_minColumn : ∀ w ∈ unitCell, (0 : ℤ) ≤ w 0 := by
  intro w hw
  rw [unitCell, Set.mem_singleton_iff] at hw
  rw [hw]; simp


theorem lmo_unitCell_reachesLeftmost :
    lmo_OrbitReachesLeftmost unitCell ucBase 0 := by
  refine ⟨2, ?_, ?_, ?_⟩
  · rw [unitCell_orbitPeriod_eq_four]; norm_num
  · rw [show ucBase.1 = ucDart0 from rfl, mpl_dartFace_iterate_ucDart2,
        mpl_dartFace_iterate_ucDart3]; rfl
  · rw [show ucBase.1 = ucDart0 from rfl, mpl_dartFace_iterate_ucDart2]
    change (-1 : ℤ) ≤ (0 : ℤ) - 1; norm_num


theorem lmo_unitCell_windingWitness : wei_WindingWitness unitCell ucBase := by
  have hcyc : (mpl_orbitLoop unitCell ucBase).IsCycle :=
    mpl_orbitLoop_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
      shw_unitCell_faceInj
  exact lmo_windingWitness_of_reachesLeftmost unitCell ucBase 0 lmo_unitCell_minColumn hcyc
    lmo_unitCell_reachesLeftmost


theorem lmo_face_col_left {e : Dart} (hd : e.dir = ![-1, 0]) :
    (dartFace e) 0 = e.tail 0 - 1 := by rw [dartFace_of_dir_left e hd]; simp


theorem lmo_face_col_up {e : Dart} (hd : e.dir = ![0, 1]) :
    (dartFace e) 0 = e.tail 0 - 1 := by rw [dartFace_of_dir_up e hd]; simp


theorem lmo_face_col_right {e : Dart} (hd : e.dir = ![1, 0]) :
    (dartFace e) 0 = e.tail 0 := by rw [dartFace_of_dir_right e hd]; simp


theorem lmo_face_col_down {e : Dart} (hd : e.dir = ![0, -1]) :
    (dartFace e) 0 = e.tail 0 := by rw [dartFace_of_dir_down e hd]; simp


theorem lmo_reachesLeftmost_of_left_tail (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (m : ℤ)
    {k : ℕ} (hk : k < dartOrbitPeriod K a)
    (htail : ((dartNext K)^[k] a.1).tail 0 = m)
    (hd : ((dartNext K)^[k] a.1).dir = ![-1, 0]) :
    lmo_OrbitReachesLeftmost K a m := by
  refine ⟨k, hk, ?_, ?_⟩
  · 
    rw [show (dartNext K)^[k + 1] a.1 = dartNext K ((dartNext K)^[k] a.1) from by
        rw [Function.iterate_succ_apply']]
    exact shw_vertStep_left K _ hd
  · rw [lmo_face_col_left hd, htail]

end Lattice
end StatMech
