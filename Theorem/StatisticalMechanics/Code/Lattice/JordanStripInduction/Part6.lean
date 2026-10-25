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
import Def.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part4
open Set SimpleGraph MeasureTheory


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem jsi_hconn_support (k k' r : ℤ) (h) (z : Site 2)
    (hz : z ∈ (jsi_hconn k k' r h).support) :
    z = jsi_cell k r ∨ z = jsi_cell k' r := by
  classical
  unfold jsi_hconn at hz
  by_cases h0 : k = k'
  · subst h0; simp only [dif_pos, SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    left; exact hz
  · simp only [dif_neg h0, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hz
    exact hz


end Lattice
end StatMech
