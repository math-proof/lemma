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
import Theorem.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part5
open Set SimpleGraph MeasureTheory


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


noncomputable def jsi_hconn (k k' r : ℤ) (h : k - k' = 1 ∨ k - k' = 0 ∨ k - k' = -1) :
    (hypercubicLattice 2).Walk (jsi_cell k r) (jsi_cell k' r) := by
  classical
  by_cases h0 : k = k'
  · exact (h0 ▸ SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk (jsi_cell k r) (jsi_cell k' r))
  · exact SimpleGraph.Walk.cons (jsi_hstep_adj k k' r (by omega)) SimpleGraph.Walk.nil


end Lattice
end StatMech
