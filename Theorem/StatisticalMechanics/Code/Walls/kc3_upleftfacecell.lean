/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean -/

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
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc3_upDart_face (e : Dart) (hd : e.dir = ![0, 1]) :
    dartFace e = ![e.tail 0 - 1, e.tail 1] :=
  dartFace_of_dir_up e hd


theorem kc3_upDart_tail (e : Dart) (hd : e.dir = ![0, 1]) :
    e.tail = ![dartFace e 0 + 1, dartFace e 1] :=
  dartFace_tail_of_dir_up e hd


theorem kc3_upDart_head (e : Dart) (hd : e.dir = ![0, 1]) :
    e.head = ![dartFace e 0 + 1, dartFace e 1 + 1] := by
  rw [dart_head_eq e, hd, dartFace_tail_of_dir_up e hd]
  funext i; fin_cases i <;> simp


theorem kc3_upDart_face_ne_tail (e : Dart) (hd : e.dir = ![0, 1]) :
    dartFace e ≠ e.tail := by
  rw [kc3_upDart_tail e hd]
  intro h; have := congrFun h 0; simp at this


theorem kc3_upDart_face_ne_head (e : Dart) (hd : e.dir = ![0, 1]) :
    dartFace e ≠ e.head := by
  rw [kc3_upDart_head e hd]
  intro h; have := congrFun h 0; simp at this


theorem kc3_leftDart_face (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] :=
  dartFace_of_dir_left e hd


theorem kc3_leftDart_tail (e : Dart) (hd : e.dir = ![-1, 0]) :
    e.tail = ![dartFace e 0 + 1, dartFace e 1 + 1] :=
  dartFace_tail_of_dir_left e hd


theorem kc3_leftDart_head (e : Dart) (hd : e.dir = ![-1, 0]) :
    e.head = ![dartFace e 0, dartFace e 1 + 1] := by
  rw [dart_head_eq e, hd, dartFace_tail_of_dir_left e hd]
  funext i; fin_cases i <;> simp


theorem kc3_leftDart_face_ne_tail (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e ≠ e.tail := by
  rw [kc3_leftDart_tail e hd]
  intro h; have := congrFun h 0; simp at this


theorem kc3_leftDart_face_ne_head (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e ≠ e.head := by
  rw [kc3_leftDart_head e hd]
  intro h; have := congrFun h 1; simp at this


theorem kc3_upLeft_faceCell {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hdir : e.dir = ![0, 1] ∨ e.dir = ![-1, 0]) :
    dartFace e ≠ e.tail ∧ dartFace e ≠ e.head ∧ e.tail ∈ K ∧ e.head ∉ K ∧
    ( (e.dir = ![0, 1] ∧ dartFace e = ![e.tail 0 - 1, e.tail 1] ∧
        e.tail = ![dartFace e 0 + 1, dartFace e 1])
    ∨ (e.dir = ![-1, 0] ∧ dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] ∧
        e.tail = ![dartFace e 0 + 1, dartFace e 1 + 1]) ) := by
  obtain ⟨htail, hhead⟩ := he
  rcases hdir with hd | hd
  · refine ⟨kc3_upDart_face_ne_tail e hd, kc3_upDart_face_ne_head e hd, htail, hhead,
      Or.inl ⟨hd, kc3_upDart_face e hd, kc3_upDart_tail e hd⟩⟩
  · refine ⟨kc3_leftDart_face_ne_tail e hd, kc3_leftDart_face_ne_head e hd, htail, hhead,
      Or.inr ⟨hd, kc3_leftDart_face e hd, kc3_leftDart_tail e hd⟩⟩


theorem kc3_dir_trichotomy_faceCell {K : Set (Site 2)} {e : Dart}
    (_he : IsBoundaryDart K e) :
    e.dir = ![1, 0] ∨ e.dir = ![0, -1] ∨
      (dartFace e ≠ e.tail ∧ dartFace e ≠ e.head) := by
  rcases dartDir_cases e with hd | hd | hd | hd
  · exact Or.inl hd
  · exact Or.inr (Or.inr ⟨kc3_leftDart_face_ne_tail e hd, kc3_leftDart_face_ne_head e hd⟩)
  · exact Or.inr (Or.inr ⟨kc3_upDart_face_ne_tail e hd, kc3_upDart_face_ne_head e hd⟩)
  · exact Or.inr (Or.inl hd)


end Walls
end StatMech
