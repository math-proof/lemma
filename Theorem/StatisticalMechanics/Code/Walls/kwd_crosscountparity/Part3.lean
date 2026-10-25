/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Def.StatisticalMechanics.Code.Walls.kwd_crosscountparity.Part3
open Finset Set SimpleGraph
open StatMech.Lattice


namespace StatMech.Walls

@[simp] theorem kwd_sideBool_eq_true (S : Set (Site 2)) (v : Site 2) :
    kwd_sideBool S v = true ↔ v ∈ S := by
  classical
  unfold kwd_sideBool; rw [decide_eq_true_iff]


theorem kwd_crossCountZ2_eq (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    kwd_crossCountZ2 S w
      = kwd_crossCount (kwd_sideBoundary (kwd_sideBool S)) w := by
  classical
  unfold kwd_crossCountZ2 kwd_crossCount
  apply List.countP_congr
  intro e _
  induction e using Sym2.ind with
  | _ a b =>
    rw [kwd_sideBoundary_mk, bdEdge_mk]
    unfold kwd_sideBool
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb]


theorem kwd_crossCountZ2_parity (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    Even (kwd_crossCountZ2 S w) ↔ (x ∈ S ↔ y ∈ S) := by
  classical
  rw [kwd_crossCountZ2_eq, kwd_crossCount_parity (kwd_sideBool S) w]
  rw [show (kwd_sideBool S x = kwd_sideBool S y) ↔ (x ∈ S ↔ y ∈ S) from ?_]
  unfold kwd_sideBool
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [hx, hy]


theorem kwd_crossCountZ2_even_of_closed (S : Set (Site 2)) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) :
    Even (kwd_crossCountZ2 S w) :=
  (kwd_crossCountZ2_parity S w).mpr Iff.rfl


theorem kwd_crossCountZ2_odd_of_separated (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) (w : (hypercubicLattice 2).Walk x y) :
    ¬ Even (kwd_crossCountZ2 S w) := by
  rw [kwd_crossCountZ2_parity]
  intro h
  exact hy (h.mp hx)

end StatMech.Walls
