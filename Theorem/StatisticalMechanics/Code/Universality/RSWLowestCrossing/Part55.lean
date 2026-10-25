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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part54
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_iUnion_rankedMinimalCandidate {I : Type*} [Fintype I]
    (W : I → Set (ConfigSpace E)) (prec : I → I → Prop) (rank : I → ℕ)
    (hrank : ∀ {j i}, prec j i → rank j < rank i) :
    (⋃ i, rlc_rankedMinimalCandidate W prec i) = ⋃ i, W i := by
  classical
  apply Set.Subset.antisymm
  · intro omega homega
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp homega
    exact Set.mem_iUnion.mpr ⟨i, hi.1⟩
  · intro omega homega
    obtain ⟨i0, hi0⟩ := Set.mem_iUnion.mp homega
    let Open : Finset I := Finset.univ.filter fun i => omega ∈ W i
    have hOpen : Open.Nonempty := ⟨i0, by simp [Open, hi0]⟩
    let R : Finset ℕ := Open.image rank
    have hR : R.Nonempty := hOpen.image rank
    let r := R.min' hR
    have hrmem : r ∈ R := R.min'_mem hR
    obtain ⟨i, hiOpen, hirank⟩ := Finset.mem_image.mp hrmem
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change omega ∈ W i ∧
      omega ∉ ⋃ j : I, if prec j i then W j else ∅
    refine ⟨(Finset.mem_filter.mp hiOpen).2, ?_⟩
    intro hlower
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hlower
    by_cases hji : prec j i
    · have hjW : omega ∈ W j := by simpa [hji] using hj
      have hjOpen : j ∈ Open := by simp [Open, hjW]
      have hjR : rank j ∈ R := Finset.mem_image.mpr ⟨j, hjOpen, rfl⟩
      have hmin : r ≤ rank j := R.min'_le _ hjR
      have hlt := hrank hji
      rw [hirank] at hlt
      exact (not_lt_of_ge hmin) hlt
    · simpa [hji] using hj


end Universality
end StatMech
