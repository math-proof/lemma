/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

noncomputable def rlc_axisGapFlipHom {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (_G : RlcAxisBarrierGap gamma gamma') :
    ((hypercubicLattice 2).induce
      (rlc_connectorAllowed gamma gamma' : Set (Site 2))) →g
    ((hypercubicLattice 2).induce
      (rlc_connectorAllowed gamma gamma' : Set (Site 2))) where
  toFun x := ⟨rlc_flipX x,
    (rlc_connectorAllowed_mem_flipX_iff gamma gamma' x).mp x.2⟩
  map_rel' := by
    intro x y hxy
    rw [SimpleGraph.induce_adj] at hxy ⊢
    exact (rlc_adj_flipX x y).mp hxy

end Universality
end StatMech
