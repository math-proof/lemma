/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Def.StatisticalMechanics.Code.Walls.kc3_tailinK
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc3_tail_isCellCorner (e : Dart) :
    kc3_IsCellCorner (dartFace e) e.tail := by
  rcases dartDir_cases e with hd | hd | hd | hd
  · 
    refine ⟨0, 0, Or.inl rfl, Or.inl rfl, ?_⟩
    rw [dartFace_tail_of_dir_right e hd]; funext i; fin_cases i <;> simp
  · 
    refine ⟨1, 1, Or.inr rfl, Or.inr rfl, ?_⟩
    rw [dartFace_tail_of_dir_left e hd]
  · 
    refine ⟨1, 0, Or.inr rfl, Or.inl rfl, ?_⟩
    rw [dartFace_tail_of_dir_up e hd]; funext i; fin_cases i <;> simp
  · 
    refine ⟨0, 1, Or.inl rfl, Or.inr rfl, ?_⟩
    rw [dartFace_tail_of_dir_down e hd]; funext i; fin_cases i <;> simp


theorem kc3_cellCorner_coord {f q : Site 2} (h : kc3_IsCellCorner f q) :
    (q 0 = f 0 ∨ q 0 = f 0 + 1) ∧ (q 1 = f 1 ∨ q 1 = f 1 + 1) := by
  obtain ⟨s, t, hs, ht, hq⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hs with rfl | rfl <;> simp [hq]
  · rcases ht with rfl | rfl <;> simp [hq]


theorem kc3_faceCorner_in_K {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e) :
    kc3_IsCellCorner (dartFace e) e.tail ∧ e.tail ∈ K :=
  ⟨kc3_tail_isCellCorner e, he.1⟩


theorem kc3_iterate_faceCorner_in_K (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    kc3_IsCellCorner (dartFace ((dartNext K)^[k] e)) ((dartNext K)^[k] e).tail ∧
      ((dartNext K)^[k] e).tail ∈ K :=
  kc3_faceCorner_in_K (kc3_iterate_isBoundaryDart K e he k)


theorem kc3_left_face_SW (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] :=
  dartFace_of_dir_left e hd


theorem kc3_left_tail_eq_NE (e : Dart) (hd : e.dir = ![-1, 0]) :
    e.tail = npd_P11 (dartFace e) := by
  rw [dartFace_tail_of_dir_left e hd, npd_P11]


theorem kc3_left_extremeCell_mem {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![-1, 0]) :
    npd_P11 (dartFace e) ∈ K := by
  rw [← kc3_left_tail_eq_NE e hd]; exact he.tail_mem


theorem kc3_left_extremeCell_mem_coord {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![-1, 0]) :
    (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) ∈ K := by
  have h := kc3_left_extremeCell_mem he hd
  rwa [npd_P11] at h


theorem kc3_left_face_ne_tail (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e ≠ e.tail := by
  rw [kc3_left_tail_eq_NE e hd]
  intro h
  have := congrFun h 0
  simp only [npd_P11, Matrix.cons_val_zero] at this
  omega


theorem kc3_tailInK_node {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e) :
    e.tail ∈ K ∧ kc3_IsCellCorner (dartFace e) e.tail ∧
      (e.dir = ![-1, 0] →
        dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] ∧
        e.tail = npd_P11 (dartFace e) ∧
        npd_P11 (dartFace e) ∈ K) := by
  refine ⟨he.tail_mem, kc3_tail_isCellCorner e, ?_⟩
  intro hd
  exact ⟨kc3_left_face_SW e hd, kc3_left_tail_eq_NE e hd, kc3_left_extremeCell_mem he hd⟩


theorem kc3_iterate_tailInK_node (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    ((dartNext K)^[k] e).tail ∈ K ∧
      kc3_IsCellCorner (dartFace ((dartNext K)^[k] e)) ((dartNext K)^[k] e).tail ∧
      (((dartNext K)^[k] e).dir = ![-1, 0] →
        dartFace ((dartNext K)^[k] e) =
          ![((dartNext K)^[k] e).tail 0 - 1, ((dartNext K)^[k] e).tail 1 - 1] ∧
        ((dartNext K)^[k] e).tail = npd_P11 (dartFace ((dartNext K)^[k] e)) ∧
        npd_P11 (dartFace ((dartNext K)^[k] e)) ∈ K) :=
  kc3_tailInK_node (kc3_iterate_isBoundaryDart K e he k)


end Walls
end StatMech
