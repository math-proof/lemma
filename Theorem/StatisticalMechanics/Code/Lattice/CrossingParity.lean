/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Def.StatisticalMechanics.Code.Lattice.CrossingParity
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

@[simp] theorem crossCount_nil (S : Set (Site 2)) (x : Site 2) :
    crossCount S (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
  classical
  simp [crossCount]

open Classical in

theorem crossCount_cons (S : Set (Site 2)) {a b c : Site 2}
    (hab : (hypercubicLattice 2).Adj a b) (p : (hypercubicLattice 2).Walk b c) :
    crossCount S (Walk.cons hab p) =
      (if bdEdge S s(a, b) then 1 else 0) + crossCount S p := by
  rw [crossCount, crossCount, SimpleGraph.Walk.edges_cons, List.countP_cons]
  by_cases h : bdEdge S s(a, b)
  · rw [if_pos h, if_pos (by simp [h])]; ring
  · rw [if_neg h, if_neg (by simp [h])]; ring


theorem crossCount_append (S : Set (Site 2)) {x y z : Site 2}
    (p : (hypercubicLattice 2).Walk x y) (q : (hypercubicLattice 2).Walk y z) :
    crossCount S (p.append q) = crossCount S p + crossCount S q := by
  classical
  rw [crossCount, crossCount, crossCount, SimpleGraph.Walk.edges_append, List.countP_append]


theorem crossCount_reverse (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    crossCount S w.reverse = crossCount S w := by
  classical
  rw [crossCount, crossCount, SimpleGraph.Walk.edges_reverse, List.countP_reverse]


theorem crossCount_parity (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    Even (crossCount S w) ↔ (x ∈ S ↔ y ∈ S) := by
  classical
  induction w with
  | nil => simp [crossCount]
  | @cons a b c hab p ih =>
    rw [crossCount, SimpleGraph.Walk.edges_cons, List.countP_cons]
    rw [crossCount] at ih
    by_cases hbd : bdEdge S s(a, b)
    · rw [if_pos (by simp [hbd]), Nat.even_add_one, ih]
      rw [bdEdge_mk] at hbd
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> by_cases hc : c ∈ S <;> simp_all
    · rw [if_neg (by simp [hbd]), add_zero, ih]
      rw [bdEdge_mk] at hbd
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> by_cases hc : c ∈ S <;> simp_all


theorem crossCount_parity_eq_of_sameEndpoints (S : Set (Site 2)) {x y : Site 2}
    (w₁ w₂ : (hypercubicLattice 2).Walk x y) :
    crossCount S w₁ % 2 = crossCount S w₂ % 2 := by
  classical
  have h1 := crossCount_parity S w₁
  have h2 := crossCount_parity S w₂
  rw [Nat.even_iff] at h1 h2
  by_cases hP : (x ∈ S ↔ y ∈ S)
  · rw [h1.mpr hP, h2.mpr hP]
  · have e1 : crossCount S w₁ % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (crossCount S w₁) with h | h
      · exact absurd (h1.mp h) hP
      · exact h
    have e2 : crossCount S w₂ % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (crossCount S w₂) with h | h
      · exact absurd (h2.mp h) hP
      · exact h
    rw [e1, e2]


theorem face_flip_parity (S : Set (Site 2)) (a b : ℤ)
    (w₁ w₂ : (hypercubicLattice 2).Walk (faceCorner00 a b) (faceCorner11 a b)) :
    crossCount S w₁ % 2 = crossCount S w₂ % 2 :=
  crossCount_parity_eq_of_sameEndpoints S w₁ w₂


theorem crossCount_even_of_loop (S : Set (Site 2)) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) : Even (crossCount S w) :=
  (crossCount_parity S w).mpr Iff.rfl


theorem crossCount_odd_of_separated (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) (w : (hypercubicLattice 2).Walk x y) :
    ¬ Even (crossCount S w) := by
  rw [crossCount_parity]
  intro h
  exact hy (h.mp hx)


end Lattice
end StatMech
