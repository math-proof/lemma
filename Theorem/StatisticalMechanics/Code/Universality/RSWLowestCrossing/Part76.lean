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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part75
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_axis_mem_connectorBarrier_iff {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (t : ℤ) :
    ![0, t] ∈ rlc_connectorBarrier gamma gamma' ↔
      ![0, t] ∈ rlc_pathVertices gamma.1 ∨
      ![0, t] ∈ rlc_pathVertices gamma'.1 := by
  classical
  let z : Site 2 := ![0, t]
  have hz : rlc_flipX z = z := rlc_flipX_eq_self_of_zero (by simp [z])
  have himage (P : Finset (Site 2)) : z ∈ P.image rlc_flipX ↔ z ∈ P := by
    constructor
    · intro h
      obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp h
      have : w = z := by
        calc
          w = rlc_flipX (rlc_flipX w) := (rlc_flipX_involutive w).symm
          _ = rlc_flipX z := congrArg rlc_flipX hwz
          _ = z := hz
      simpa [this] using hw
    · intro h
      exact Finset.mem_image.mpr ⟨z, h, hz⟩
  change z ∈ rlc_connectorBarrier gamma gamma' ↔ _
  simp only [rlc_connectorBarrier, Finset.mem_union, himage]
  tauto

end Universality
end StatMech
