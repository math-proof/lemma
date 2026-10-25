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
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part39
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


noncomputable def rlc_rot180LeftAvoidHom {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_leftPathAvoidGraph gamma →g
      rlc_rightPathAvoidGraph (rlc_rot180LeftPath gamma) where
  toFun := rlc_rot180
  map_rel' := by
    intro u v h
    refine ⟨(rlc_adj_rot180 u v).mp h.1,
      (rlc_rot180_mem_leftRect_iff_rightRect n u).mp h.2.1,
      (rlc_rot180_mem_leftRect_iff_rightRect n v).mp h.2.2.1, ?_, ?_⟩
    · intro hu
      rw [rlc_pathVertices_rot180LeftPath, Finset.mem_image] at hu
      obtain ⟨z, hz, hzu⟩ := hu
      have hzu' : z = u := rlc_rot180.injective (by simpa using hzu)
      exact h.2.2.2.1 (hzu' ▸ hz)
    · intro hv
      rw [rlc_pathVertices_rot180LeftPath, Finset.mem_image] at hv
      obtain ⟨z, hz, hzv⟩ := hv
      have hzv' : z = v := rlc_rot180.injective (by simpa using hzv)
      exact h.2.2.2.2 (hzv' ▸ hz)

end Universality
end StatMech
