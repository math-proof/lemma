/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part74
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


@[simp] theorem rlc_mem_axisHeights_iff (P : Finset (Site 2)) (t : ℤ) :
    t ∈ rlc_axisHeights P ↔ ![0, t] ∈ P := by
  classical
  constructor
  · intro ht
    obtain ⟨z, hz, hzt⟩ := Finset.mem_image.mp ht
    have hz0 : z 0 = 0 := (Finset.mem_filter.mp hz).2
    have hz1 : z 1 = t := hzt
    have : z = ![0, t] := by
      funext i
      fin_cases i <;> simp [hz0, hz1]
    simpa [this] using (Finset.mem_filter.mp hz).1
  · intro ht
    apply Finset.mem_image.mpr
    exact ⟨![0, t], by simp [ht], by simp⟩


theorem rlc_exists_finset_gap (A B : Finset ℤ) {x y : ℤ}
    (hx : x ∈ A) (hy : y ∈ B) (hxy : x < y) :
    ∃ a b : ℤ, a ∈ A ∧ b ∈ B ∧ x ≤ a ∧ a < b ∧
      b ≤ y ∧ ∀ t : ℤ, a < t → t < b → t ∉ A ∧ t ∉ B := by
  classical
  let Bup := B.filter fun t => x < t
  have hBup : Bup.Nonempty := ⟨y, by simp [Bup, hy, hxy]⟩
  let b := Bup.min' hBup
  have hbBup : b ∈ Bup := Bup.min'_mem hBup
  have hbB : b ∈ B := (Finset.mem_filter.mp hbBup).1
  have hxb : x < b := (Finset.mem_filter.mp hbBup).2
  have hby : b ≤ y := Bup.min'_le y (by simp [Bup, hy, hxy])
  let Adown := A.filter fun t => t < b
  have hAdown : Adown.Nonempty := ⟨x, by simp [Adown, hx, hxb]⟩
  let a := Adown.max' hAdown
  have haAdown : a ∈ Adown := Adown.max'_mem hAdown
  have haA : a ∈ A := (Finset.mem_filter.mp haAdown).1
  have hab : a < b := (Finset.mem_filter.mp haAdown).2
  have hxa : x ≤ a := Adown.le_max' x (by simp [Adown, hx, hxb])
  refine ⟨a, b, haA, hbB, hxa, hab, hby, ?_⟩
  intro t hat htb
  constructor
  · intro htA
    have htAdown : t ∈ Adown := by simp [Adown, htA, htb]
    exact (not_lt_of_ge (Adown.le_max' t htAdown)) hat
  · intro htB
    have hxt : x < t := lt_of_le_of_lt hxa hat
    have htBup : t ∈ Bup := by simp [Bup, htB, hxt]
    exact (not_lt_of_ge (Bup.min'_le t htBup)) htb


end Universality
end StatMech
