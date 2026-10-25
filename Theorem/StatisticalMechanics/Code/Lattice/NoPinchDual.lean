/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Def.StatisticalMechanics.Code.Lattice.NoPinchDual
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem npd_corners_right {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![1, 0]) :
    npd_P00 (dartFace e) ∈ K ∧ npd_P10 (dartFace e) ∉ K := by
  have htail : e.tail = npd_P00 (dartFace e) := dartFace_tail_of_dir_right e hd
  have hhead : e.head = npd_P10 (dartFace e) := by
    rw [dart_head_eq e, hd, htail, npd_P00, npd_P10]
    funext i; fin_cases i <;> simp
  exact ⟨htail ▸ he.1, hhead ▸ he.2⟩


theorem npd_corners_up {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![0, 1]) :
    npd_P10 (dartFace e) ∈ K ∧ npd_P11 (dartFace e) ∉ K := by
  have htail : e.tail = npd_P10 (dartFace e) := by
    rw [dartFace_tail_of_dir_up e hd, npd_P10]
  have hhead : e.head = npd_P11 (dartFace e) := by
    rw [dart_head_eq e, hd, dartFace_tail_of_dir_up e hd, npd_P11]
    funext i; fin_cases i <;> simp
  exact ⟨htail ▸ he.1, hhead ▸ he.2⟩


theorem npd_corners_left {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![-1, 0]) :
    npd_P11 (dartFace e) ∈ K ∧ npd_P01 (dartFace e) ∉ K := by
  have htail : e.tail = npd_P11 (dartFace e) := by
    rw [dartFace_tail_of_dir_left e hd, npd_P11]
  have hhead : e.head = npd_P01 (dartFace e) := by
    rw [dart_head_eq e, hd, dartFace_tail_of_dir_left e hd, npd_P01]
    funext i; fin_cases i <;> simp
  exact ⟨htail ▸ he.1, hhead ▸ he.2⟩


theorem npd_corners_down {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![0, -1]) :
    npd_P01 (dartFace e) ∈ K ∧ npd_P00 (dartFace e) ∉ K := by
  have htail : e.tail = npd_P01 (dartFace e) := by
    rw [dartFace_tail_of_dir_down e hd, npd_P01]
  have hhead : e.head = npd_P00 (dartFace e) := by
    rw [dart_head_eq e, hd, dartFace_tail_of_dir_down e hd, npd_P00]
    funext i; fin_cases i <;> simp
  exact ⟨htail ▸ he.1, hhead ▸ he.2⟩


end Lattice
end StatMech
