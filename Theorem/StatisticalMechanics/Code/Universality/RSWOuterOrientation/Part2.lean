/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterOrientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWArcBadPlacement.Part6
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Def.StatisticalMechanics.Code.Universality.RSWOuterOrientation
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_outerExitDart_isBoundary {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    IsBoundaryDart (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitDart G omega) := by
  let v : Site 2 := gamma.1.2.1
  have hvPath : v ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨v, by simpa [v] using rightSide_subset gamma.1.2.1.2⟩,
      gamma.1.2.2.1.end_mem_support, rfl⟩
  have hv : v ∈ rlc_mixedWiredReachSet G omega :=
    rlc_rightPathVertex_mem_mixedWiredReachSet G omega hvPath
  have hvx : v 0 = 2 * n := by
    simpa only [v] using gamma.1.2.1.2.2
  constructor
  · simpa [rlc_outerExitDart, v] using hv
  · intro hhead
    have hbox := rlc_mixedWiredReachSet_subset_box G omega hhead
    rw [mem_rect] at hbox
    have hheadx : (rlc_outerExitDart G omega).head 0 = 2 * n + 1 := by
      simp [rlc_outerExitDart, v, hvx]
    omega


end Universality
end StatMech
