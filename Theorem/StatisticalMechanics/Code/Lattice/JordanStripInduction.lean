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
open Set SimpleGraph MeasureTheory


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem jsi_adj_cases (u v : Site 2) (hadj : (hypercubicLattice 2).Adj u v) :
    (u 1 = v 1 ∧ (u 0 - v 0 = 1 ∨ u 0 - v 0 = -1)) ∨
    (u 0 = v 0 ∧ (u 1 - v 1 = 1 ∨ u 1 - v 1 = -1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have key : ((u 0 - v 0).natAbs = 1 ∧ (u 1 - v 1).natAbs = 0) ∨
             ((u 0 - v 0).natAbs = 0 ∧ (u 1 - v 1).natAbs = 1) := by omega
  rcases key with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · left; exact ⟨by omega, by omega⟩
  · right; exact ⟨by omega, by omega⟩


end Lattice
end StatMech
