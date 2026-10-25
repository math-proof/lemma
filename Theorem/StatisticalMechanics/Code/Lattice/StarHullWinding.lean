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
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem shw_vertStep_right (K : Set (Site 2)) (e : Dart) (hd : e.dir = ![1, 0]) :
    (dartFace e) 0 = (dartFace (dartNext K e)) 0 := by
  rw [dartFace_of_dir_right e hd, dartFace_next_of_dir_right K e hd]; simp


theorem shw_vertStep_left (K : Set (Site 2)) (e : Dart) (hd : e.dir = ![-1, 0]) :
    (dartFace e) 0 = (dartFace (dartNext K e)) 0 := by
  rw [dartFace_of_dir_left e hd, dartFace_next_of_dir_left K e hd]; simp


theorem shw_vertStep_dir (K : Set (Site 2)) (e : Dart)
    (hv : (dartFace e) 0 = (dartFace (dartNext K e)) 0) :
    e.dir = ![1, 0] ∨ e.dir = ![-1, 0] := by
  rcases dartDir_cases e with hd | hd | hd | hd
  · exact Or.inl hd
  · exact Or.inr hd
  · exfalso
    rw [dartFace_of_dir_up e hd, dartFace_next_of_dir_up K e hd] at hv
    simp only [Matrix.cons_val_zero] at hv; omega
  · exfalso
    rw [dartFace_of_dir_down e hd, dartFace_next_of_dir_down K e hd] at hv
    simp only [Matrix.cons_val_zero] at hv; omega


theorem shw_extremeCell_eq_tail_of_left (e : Dart) (hd : e.dir = ![-1, 0]) :
    (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) = e.tail :=
  (dartFace_tail_of_dir_left e hd).symm


theorem shw_extremeCell_mem_of_left {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![-1, 0]) :
    (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) ∈ K := by
  rw [shw_extremeCell_eq_tail_of_left e hd]; exact he.tail_mem


theorem shw_extremeCell_notMem_of_right {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![1, 0]) :
    (![dartFace e 0 + 1, dartFace e 1] : Site 2) ∉ K := by
  have h := (npd_corners_right he hd).2
  unfold npd_P10 at h
  exact h


theorem shw_mpl_edges_form (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitLoop K a).edges
      = (List.range (dartOrbitPeriod K a)).map
        (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
  rw [mpl_orbitLoop_edges, mpl_orbitFaceLoop, SimpleGraph.Walk.edges_copy, orbitFaceWalk_edges]


theorem shw_exists_vertStep (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hcyc : (mpl_orbitLoop K a).IsCycle) :
    ∃ k < dartOrbitPeriod K a,
      (dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0 := by
  obtain ⟨i, hi, hvert⟩ := eaw_exists_vertEdge (mpl_orbitLoop K a) hcyc
  have hmem : s((mpl_orbitLoop K a).getVert i, (mpl_orbitLoop K a).getVert (i + 1)) ∈
      (mpl_orbitLoop K a).edges := eaw_getVert_edge_mem (mpl_orbitLoop K a) hi
  rw [shw_mpl_edges_form] at hmem
  rw [List.mem_map] at hmem
  obtain ⟨k, hk, heq⟩ := hmem
  rw [List.mem_range] at hk
  refine ⟨k, hk, ?_⟩
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact hvert
  · rw [h1, h2]; exact hvert.symm


theorem shw_minCol_le_of_vertEdge (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (c : ℤ)
    (hmin : ∀ k < dartOrbitPeriod K a,
      (dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0 →
        c ≤ (dartFace ((dartNext K)^[k] a.1)) 0)
    {x y : Site 2} (hxy : s(x, y) ∈ (mpl_orbitLoop K a).edges) (hcol : x 0 = y 0) : c ≤ x 0 := by
  rw [shw_mpl_edges_form] at hxy
  rw [List.mem_map] at hxy
  obtain ⟨k, hk, heq⟩ := hxy
  rw [List.mem_range] at hk
  rw [Sym2.eq_iff] at heq
  
  rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · 
    have hv : (dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0 := by
      rw [h1, h2]; exact hcol
    have := hmin k hk hv
    rw [← h1]; exact this
  · 
    have hv : (dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0 := by
      rw [h1, h2]; exact hcol.symm
    have hle := hmin k hk hv
    
    rw [← h2, ← hv]; exact hle


theorem shw_minVertStep_exists (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hcyc : (mpl_orbitLoop K a).IsCycle) :
    ∃ k < dartOrbitPeriod K a,
      ((dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0) ∧
      (∀ j < dartOrbitPeriod K a,
        (dartFace ((dartNext K)^[j] a.1)) 0 = (dartFace ((dartNext K)^[j + 1] a.1)) 0 →
          (dartFace ((dartNext K)^[k] a.1)) 0 ≤ (dartFace ((dartNext K)^[j] a.1)) 0) := by
  classical
  obtain ⟨k0, hk0, hv0⟩ := shw_exists_vertStep K a hcyc
  set p := dartOrbitPeriod K a with hp
  set S := (Finset.range p).filter
    (fun k => (dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0)
    with hS
  have hSne : S.Nonempty := ⟨k0, by rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨hk0, hv0⟩⟩
  obtain ⟨k, hkS, hkmin⟩ := S.exists_min_image (fun k => (dartFace ((dartNext K)^[k] a.1)) 0) hSne
  rw [hS, Finset.mem_filter, Finset.mem_range] at hkS
  refine ⟨k, hkS.1, hkS.2, ?_⟩
  intro j hj hvj
  have hjS : j ∈ S := by rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hvj⟩
  exact hkmin j hjS


end Lattice
end StatMech
