/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_tailinK.lean -/

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
import Def.StatisticalMechanics.Code.Walls.kc2_tailinK
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc2_tail_isCellCorner (e : Dart) :
    kc2_IsCellCorner (dartFace e) e.tail := by
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


theorem kc2_faceCorner_in_K {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e) :
    kc2_IsCellCorner (dartFace e) e.tail ∧ e.tail ∈ K :=
  ⟨kc2_tail_isCellCorner e, he.1⟩


theorem kc2_iterate_faceCorner_in_K (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    kc2_IsCellCorner (dartFace ((dartNext K)^[k] e)) ((dartNext K)^[k] e).tail ∧
      ((dartNext K)^[k] e).tail ∈ K :=
  kc2_faceCorner_in_K (kc2_iterate_isBoundaryDart K e he k)


theorem kc2_cellCorner_coord {f q : Site 2} (h : kc2_IsCellCorner f q) :
    (q 0 = f 0 ∨ q 0 = f 0 + 1) ∧ (q 1 = f 1 ∨ q 1 = f 1 + 1) := by
  obtain ⟨s, t, hs, ht, hq⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hs with rfl | rfl <;> simp [hq]
  · rcases ht with rfl | rfl <;> simp [hq]

end Walls
end StatMech
