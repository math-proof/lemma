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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part15
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_flipY_lrRestricted_iff (a b n : ℤ) (L R : Set (Site 2))
    (omega : ConfigSpace (Sym2 (Site 2))) :
    omega ∈ rlc_lrRestrictedEvent a b (-n) n L R →
      rlc_flipYConfig omega ∈ rlc_lrRestrictedEvent a b (-n) n
        (rlc_flipY '' L) (rlc_flipY '' R) := by
  rintro ⟨x, y, hxL, hyR, hxy⟩
  let xf : leftSide a b (-n) n :=
    ⟨rlc_flipY (x : Site 2), (rlc_mem_leftSide_flipY a b n x).mp x.2⟩
  let yf : rightSide a b (-n) n :=
    ⟨rlc_flipY (y : Site 2), (rlc_mem_rightSide_flipY a b n y).mp y.2⟩
  refine ⟨xf, yf, ⟨x, hxL, rfl⟩, ⟨y, hyR, rfl⟩, ?_⟩
  exact hxy.map (rlc_flipYInducedHom a b n omega)

theorem rlc_flipY_image_univ : rlc_flipY '' (Set.univ : Set (Site 2)) = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨rlc_flipY x, Set.mem_univ _, rlc_flipY_involutive x⟩

theorem rlc_flipY_image_upper : rlc_flipY '' rlc_upperHalf = rlc_lowerHalf := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change 0 ≤ y 1 at hy
    change -(y 1) ≤ 0
    omega
  · intro hx
    change x 1 ≤ 0 at hx
    refine ⟨rlc_flipY x, ?_, rlc_flipY_involutive x⟩
    change 0 ≤ -(x 1)
    omega

theorem rlc_flipY_image_lower : rlc_flipY '' rlc_lowerHalf = rlc_upperHalf := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y 1 ≤ 0 at hy
    change 0 ≤ -(y 1)
    omega
  · intro hx
    change 0 ≤ x 1 at hx
    refine ⟨rlc_flipY x, ?_, rlc_flipY_involutive x⟩
    change -(x 1) ≤ 0
    omega

end Universality
end StatMech
