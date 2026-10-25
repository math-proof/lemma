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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part10
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_lrRestrictedEvent_isIncreasing (a b c d : ℤ) (L R : Set (Site 2)) :
    IsIncreasing (rlc_lrRestrictedEvent a b c d L R) := by
  intro omega omega' homega hle
  obtain ⟨x, y, hx, hy, hxy⟩ := hle
  exact ⟨x, y, hx, hy, StatMech.TwoDim.connectedWithin_mono homega hxy⟩


theorem rlc_lrRestrictedEvent_dependsOn (a b c d : ℤ) (L R : Set (Site 2)) :
    DependsOn ((rlc_lrRestrictedEvent a b c d L R).indicator
      (fun _ => (1 : ℝ)))
      (edgesWithinFinset (rect_finite a b c d).toFinset : Set (Sym2 (Site 2))) := by
  let S := (rect_finite a b c d).toFinset
  have hSco : (S : Set (Site 2)) = rect a b c d := by
    ext z
    simp [S]
  intro omega omega' hagree
  have hconn : ∀ (x y : Site 2),
      (∃ (hx : x ∈ rect a b c d) (hy : y ∈ rect a b c d),
        ConnectedWithin 2 omega (rect a b c d) ⟨x, hx⟩ ⟨y, hy⟩) ↔
      (∃ (hx : x ∈ rect a b c d) (hy : y ∈ rect a b c d),
        ConnectedWithin 2 omega' (rect a b c d) ⟨x, hx⟩ ⟨y, hy⟩) := by
    intro x y
    rw [← hSco]
    exact withinConn_congr S x y hagree
  have hevent : omega ∈ rlc_lrRestrictedEvent a b c d L R ↔
      omega' ∈ rlc_lrRestrictedEvent a b c d L R := by
    constructor
    · rintro ⟨x, y, hx, hy, hxy⟩
      have hc : ∃ (hx' : (x : Site 2) ∈ rect a b c d)
          (hy' : (y : Site 2) ∈ rect a b c d),
          ConnectedWithin 2 omega (rect a b c d) ⟨x, hx'⟩ ⟨y, hy'⟩ :=
        ⟨leftSide_subset x.2, rightSide_subset y.2, hxy⟩
      obtain ⟨_, _, hc'⟩ := (hconn x y).mp hc
      exact ⟨x, y, hx, hy, hc'⟩
    · rintro ⟨x, y, hx, hy, hxy⟩
      have hc : ∃ (hx' : (x : Site 2) ∈ rect a b c d)
          (hy' : (y : Site 2) ∈ rect a b c d),
          ConnectedWithin 2 omega' (rect a b c d) ⟨x, hx'⟩ ⟨y, hy'⟩ :=
        ⟨leftSide_subset x.2, rightSide_subset y.2, hxy⟩
      obtain ⟨_, _, hc'⟩ := (hconn x y).mpr hc
      exact ⟨x, y, hx, hy, hc'⟩
  by_cases hmem : omega ∈ rlc_lrRestrictedEvent a b c d L R
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]

end Universality
end StatMech
