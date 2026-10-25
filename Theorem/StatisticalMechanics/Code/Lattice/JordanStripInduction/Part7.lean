/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part3
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part5
open Set SimpleGraph MeasureTheory


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem jsi_arcWalk_zero (col : ℤ → ℤ) (hsh) (c : ℤ) :
    jsi_arcWalk col hsh c 0 = (SimpleGraph.Walk.nil).copy rfl (by rw [jsi_cell_eq]; norm_num) := rfl


theorem jsi_arcWalk_succ (col : ℤ → ℤ) (hsh) (c : ℤ) (n : ℕ) :
    jsi_arcWalk col hsh c (n + 1) =
      (((jsi_arcWalk col hsh c n).append
        (SimpleGraph.Walk.cons (jsi_vstep_adj (col (c + (n : ℤ))) (c + (n : ℤ)))
          (jsi_hconn (col (c + (n : ℤ))) (col (c + (n : ℤ) + 1)) (c + (n : ℤ) + 1)
            (by have := hsh (c + (n : ℤ)); omega)))).copy rfl (by
              have heq : c + (n : ℤ) + 1 = c + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
              rw [jsi_cell_eq]; exact ⟨by rw [heq], heq⟩)) := rfl


theorem jsi_arcWalk_support_subset (P : Set (Site 2)) (col : ℤ → ℤ) (hsh) (c : ℤ) :
    (n : ℕ) →
    (hP : ∀ j : ℕ, j ≤ n → jsi_cell (col (c + j)) (c + j) ∈ P) →
    (hPc : ∀ j : ℕ, j < n → jsi_cell (col (c + j)) (c + j + 1) ∈ P) →
    (z : Site 2) → z ∈ (jsi_arcWalk col hsh c n).support → z ∈ P
  | 0, hP, _, z, hz => by
      rw [jsi_arcWalk_zero, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_nil,
        List.mem_singleton] at hz
      have h0 := hP 0 (le_refl 0)
      rw [hz]; simpa using h0
  | (n + 1), hP, hPc, z, hz => by
      rw [jsi_arcWalk_succ, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with h | h
      · exact jsi_arcWalk_support_subset P col hsh c n
          (fun j hj => hP j (by omega)) (fun j hj => hPc j (by omega)) z h
      · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at h
        rcases h with h | h
        · subst h; simpa using hP n (by omega)
        · rcases jsi_hconn_support _ _ _ _ z h with h1 | h1
          · subst h1; simpa using hPc n (by omega)
          · subst h1
            have heq : (c : ℤ) + (n : ℤ) + 1 = c + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
            rw [(jsi_cell_eq _ _ _ _).mpr ⟨by rw [heq], heq⟩]; exact hP (n + 1) (le_refl _)


end Lattice
end StatMech
