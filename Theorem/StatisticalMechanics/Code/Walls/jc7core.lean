/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc4_firstreturnK.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc4_tailnotprobed
import Theorem.StatisticalMechanics.Code.Walls.jc5_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc5_footprintdartsfinite
import Theorem.StatisticalMechanics.Code.Walls.jc6_ivt.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7ivtnohop
import Theorem.StatisticalMechanics.Code.Walls.jc7getverteqdartface
import Theorem.StatisticalMechanics.Code.Walls.jc7loopiscycle
import Theorem.StatisticalMechanics.Code.Walls.jc7loopseparates.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7stepfacebridge
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc7_head_eq (e : Dart) : e.head = e.tail + e.dir := by
  rw [Dart.dir_def]; abel


theorem jc7_face_row_le_one_of_tail (e : Dart) :
    (dartFace e 1 - e.tail 1).natAbs ≤ 1 := by
  rcases dartDir_cases e with h | h | h | h
  · rw [dartFace_of_dir_right e h]; simp
  · rw [dartFace_of_dir_left e h]; simp
  · rw [dartFace_of_dir_up e h]; simp
  · rw [dartFace_of_dir_down e h]; simp


theorem jc7_face_row_dist_tailTravel_le_two (e : Dart) :
    (dartFace e 1 - jc_tailTravel e 1).natAbs ≤ 2 := by
  rw [jc_tailTravel_eq]
  rcases dartDir_cases e with h | h | h | h <;>
  · first
      | rw [dartFace_of_dir_right e h]
      | rw [dartFace_of_dir_left e h]
      | rw [dartFace_of_dir_up e h]
      | rw [dartFace_of_dir_down e h]
    simp only [Pi.add_apply, Pi.neg_apply, h, rot90Fun,
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    omega


theorem jc7_face_row_dist_headTravel_le_two (e : Dart) :
    (dartFace e 1 - jc_headTravel e 1).natAbs ≤ 2 := by
  rw [jc_headTravel_eq, jc7_head_eq e]
  rcases dartDir_cases e with h | h | h | h <;>
  · first
      | rw [dartFace_of_dir_right e h]
      | rw [dartFace_of_dir_left e h]
      | rw [dartFace_of_dir_up e h]
      | rw [dartFace_of_dir_down e h]
    simp only [Pi.add_apply, Pi.neg_apply, h, rot90Fun,
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    omega


theorem jc7_footprint_row_le_one (r x : Site 2) (hx : x ∈ jc3_earFootprint r) :
    (x 1 - r 1).natAbs ≤ 1 := by
  rw [jc3_mem_earFootprint] at hx
  rcases hx with h | h | h | h | h <;> subst h
  · simp
  all_goals
    simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    omega


theorem jc7_touching_face_row_band (r : Site 2) (e : Dart)
    (h : jc5_ProbesEarFootprint r e) :
    (dartFace e 1 - r 1).natAbs ≤ 3 := by
  rcases h with hhead | htail
  · have h1 : (dartFace e 1 - jc_headTravel e 1).natAbs ≤ 2 :=
      jc7_face_row_dist_headTravel_le_two e
    have h2 : (jc_headTravel e 1 - r 1).natAbs ≤ 1 := jc7_footprint_row_le_one r _ hhead
    omega
  · have h1 : (dartFace e 1 - jc_tailTravel e 1).natAbs ≤ 2 :=
      jc7_face_row_dist_tailTravel_le_two e
    have h2 : (jc_tailTravel e 1 - r 1).natAbs ≤ 1 := jc7_footprint_row_le_one r _ htail
    omega


theorem jc7_touching_face_row_band' (r : Site 2) (e : Dart)
    (h : jc5_ProbesEarFootprint r e) :
    r 1 - 3 ≤ dartFace e 1 ∧ dartFace e 1 ≤ r 1 + 3 := by
  have := jc7_touching_face_row_band r e h
  omega


theorem jc7_touching_iff_probes (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (i : ℕ) :
    ¬ jc4_FootprintFree K a r i ↔
      jc5_ProbesEarFootprint r ((dartNext K)^[i] a.1) := by
  unfold jc4_FootprintFree
  exact jc5_not_avoidsEarFootprint_iff_probes r _


theorem jc7_touching_orbitFace_row_band (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) (i : ℕ)
    (h : ¬ jc4_FootprintFree K a r i) :
    (dartFace ((dartNext K)^[i] a.1) 1 - r 1).natAbs ≤ 3 :=
  jc7_touching_face_row_band r _ ((jc7_touching_iff_probes K a r i).mp h)


theorem jc7_touching_loopVert_row_band (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (i : ℕ)
    (hi : i ≤ (olb_orbitLoop K hK e he).length)
    (h : ¬ jc4_FootprintFree K ⟨e, he⟩ r i) :
    ((olb_orbitLoop K hK e he).getVert i 1 - r 1).natAbs ≤ 3 := by
  rw [jc7_getVert_eq_dartFace K hK e he i hi]
  exact jc7_touching_orbitFace_row_band K ⟨e, he⟩ r i h


end Walls
end StatMech
