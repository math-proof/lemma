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
import Def.StatisticalMechanics.Code.Lattice.LexMinOrientation.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem lmo_leftDartAt_dir (z₀ : Site 2) : (lmo_leftDartAt z₀).dir = ![-1, 0] := by
  rw [lmo_leftDartAt, mkDart_dir]

@[simp] theorem lmo_leftDartAt_tail (z₀ : Site 2) : (lmo_leftDartAt z₀).tail = z₀ := by
  rw [lmo_leftDartAt, mkDart_tail]

theorem lmo_leftDartAt_head (z₀ : Site 2) :
    (lmo_leftDartAt z₀).head = ![z₀ 0 - 1, z₀ 1] := by
  rw [lmo_leftDartAt, mkDart_head]; funext i; fin_cases i <;> (simp; try ring)


theorem lmo_leftDartAt_isBoundaryDart {K : Set (Site 2)} {z₀ : Site 2} (hz₀ : z₀ ∈ K)
    (hwest : (![z₀ 0 - 1, z₀ 1] : Site 2) ∉ K) :
    IsBoundaryDart K (lmo_leftDartAt z₀) := by
  refine ⟨?_, ?_⟩
  · rw [lmo_leftDartAt_tail]; exact hz₀
  · rw [lmo_leftDartAt_head]; exact hwest


theorem lmo_leftDartAt_face (z₀ : Site 2) :
    dartFace (lmo_leftDartAt z₀) = ![z₀ 0 - 1, z₀ 1 - 1] := by
  rw [dartFace_of_dir_left _ (lmo_leftDartAt_dir z₀), lmo_leftDartAt_tail]


theorem lmo_vertStep_dir {K : Set (Site 2)} (e : Dart)
    (hv : (dartFace e) 0 = (dartFace (dartNext K e)) 0) :
    e.dir = ![1, 0] ∨ e.dir = ![-1, 0] := by
  rcases dartDir_cases e with hd | hd | hd | hd
  · exact Or.inl hd
  · exact Or.inr hd
  · exfalso; rw [dartFace_of_dir_up e hd, dartFace_next_of_dir_up K e hd] at hv
    simp only [Matrix.cons_val_zero] at hv; omega
  · exfalso; rw [dartFace_of_dir_down e hd, dartFace_next_of_dir_down K e hd] at hv
    simp only [Matrix.cons_val_zero] at hv; omega


theorem lmo_vertStep_left_of_minCol {K : Set (Site 2)} (m : ℤ) (hm : ∀ w ∈ K, m ≤ w 0)
    {e : Dart} (he : IsBoundaryDart K e)
    (hvert : (dartFace e) 0 = (dartFace (dartNext K e)) 0)
    (hcol : (dartFace e) 0 ≤ m - 1) :
    e.dir = ![-1, 0] := by
  rcases lmo_vertStep_dir e hvert with hd | hd
  · exfalso
    have h := (npd_corners_right he hd).1
    rw [npd_P00] at h
    have := hm _ h
    simp only [Matrix.cons_val_zero] at this
    omega
  · exact hd


end Lattice
end StatMech
