/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc2_P00_eq_self (f : Site 2) : npd_P00 f = f := by
  funext i; fin_cases i <;> simp [npd_P00]


theorem kc2_leftDart_face (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] :=
  dartFace_of_dir_left e hd


theorem kc2_leftDart_tail_eq_P11 (e : Dart) (hd : e.dir = ![-1, 0]) :
    e.tail = npd_P11 (dartFace e) := by
  rw [dartFace_tail_of_dir_left e hd, npd_P11]


theorem kc2_leftDart_head_eq_P01 (e : Dart) (hd : e.dir = ![-1, 0]) :
    e.head = npd_P01 (dartFace e) := by
  rw [dart_head_eq e, hd, dartFace_tail_of_dir_left e hd, npd_P01]
  funext i; fin_cases i <;> simp


theorem kc2_leftDart_corners {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hd : e.dir = ![-1, 0]) :
    npd_P11 (dartFace e) ∈ K ∧ npd_P01 (dartFace e) ∉ K :=
  npd_corners_left he hd


theorem kc2_upDart_face (e : Dart) (hd : e.dir = ![0, 1]) :
    dartFace e = ![e.tail 0 - 1, e.tail 1] :=
  dartFace_of_dir_up e hd


theorem kc2_upDart_tail_eq_P10 (e : Dart) (hd : e.dir = ![0, 1]) :
    e.tail = npd_P10 (dartFace e) := by
  rw [dartFace_tail_of_dir_up e hd, npd_P10]


theorem kc2_upDart_head_eq_P11 (e : Dart) (hd : e.dir = ![0, 1]) :
    e.head = npd_P11 (dartFace e) := by
  rw [dart_head_eq e, hd, dartFace_tail_of_dir_up e hd, npd_P11]
  funext i; fin_cases i <;> simp


theorem kc2_upDart_corners {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hd : e.dir = ![0, 1]) :
    npd_P10 (dartFace e) ∈ K ∧ npd_P11 (dartFace e) ∉ K :=
  npd_corners_up he hd


theorem kc2_P00_ne_P11 (f : Site 2) : npd_P00 f ≠ npd_P11 f := by
  intro h; have := congrFun h 0; simp [npd_P00, npd_P11] at this


theorem kc2_P00_ne_P10 (f : Site 2) : npd_P00 f ≠ npd_P10 f := by
  intro h; have := congrFun h 0; simp [npd_P00, npd_P10] at this


theorem kc2_leftDart_face_ne_tail (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e ≠ e.tail := by
  rw [kc2_leftDart_tail_eq_P11 e hd]
  conv_lhs => rw [← kc2_P00_eq_self (dartFace e)]
  exact kc2_P00_ne_P11 (dartFace e)


theorem kc2_upDart_face_ne_tail (e : Dart) (hd : e.dir = ![0, 1]) :
    dartFace e ≠ e.tail := by
  rw [kc2_upDart_tail_eq_P10 e hd]
  conv_lhs => rw [← kc2_P00_eq_self (dartFace e)]
  exact kc2_P00_ne_P10 (dartFace e)


theorem kc2_leftUp_faceCell {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hdir : e.dir = ![-1, 0] ∨ e.dir = ![0, 1]) :
    dartFace e = npd_P00 (dartFace e) ∧
    npd_P00 (dartFace e) ≠ e.tail ∧
    ( (e.dir = ![-1, 0] ∧ dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] ∧
        e.tail = npd_P11 (dartFace e) ∧ npd_P11 (dartFace e) ∈ K)
    ∨ (e.dir = ![0, 1] ∧ dartFace e = ![e.tail 0 - 1, e.tail 1] ∧
        e.tail = npd_P10 (dartFace e) ∧ npd_P10 (dartFace e) ∈ K) ) := by
  refine ⟨(kc2_P00_eq_self _).symm, ?_, ?_⟩
  · rcases hdir with hd | hd
    · rw [kc2_P00_eq_self]; exact kc2_leftDart_face_ne_tail e hd
    · rw [kc2_P00_eq_self]; exact kc2_upDart_face_ne_tail e hd
  · rcases hdir with hd | hd
    · exact Or.inl ⟨hd, kc2_leftDart_face e hd, kc2_leftDart_tail_eq_P11 e hd,
        (kc2_leftDart_corners he hd).1⟩
    · exact Or.inr ⟨hd, kc2_upDart_face e hd, kc2_upDart_tail_eq_P10 e hd,
        (kc2_upDart_corners he hd).1⟩


theorem kc2_dir_trichotomy_faceCell {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) :
    e.dir = ![1, 0] ∨ e.dir = ![0, -1] ∨
      (dartFace e = npd_P00 (dartFace e) ∧ npd_P00 (dartFace e) ≠ e.tail) := by
  rcases dartDir_cases e with hd | hd | hd | hd
  · exact Or.inl hd
  · have h := kc2_leftUp_faceCell he (Or.inl hd)
    exact Or.inr (Or.inr ⟨h.1, h.2.1⟩)
  · have h := kc2_leftUp_faceCell he (Or.inr hd)
    exact Or.inr (Or.inr ⟨h.1, h.2.1⟩)
  · exact Or.inr (Or.inl hd)


end Walls
end StatMech
