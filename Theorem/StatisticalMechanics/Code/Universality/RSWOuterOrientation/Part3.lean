/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterOrientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWArcBadPlacement.Part6
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Def.StatisticalMechanics.Code.Universality.RSWOuterOrientation.Part2
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_outerExitOrbit_head_reachable {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) (k : ℕ) :
    let K := rlc_mixedWiredReachSet G omega
    let e := rlc_outerExitDart G omega
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨e.head, (rlc_outerExitDart_isBoundary G omega).2⟩
      ⟨((dartNext K)^[k] e).head,
        (iterate_isBoundaryDart' K e
          (rlc_outerExitDart_isBoundary G omega) k).2⟩ := by
  dsimp only
  exact dartNext_orbit_head_sameComponent
    (rlc_mixedWiredReachSet G omega)
    (rlc_outerExitDart G omega)
    ((dartNext (rlc_mixedWiredReachSet G omega))^[k]
      (rlc_outerExitDart G omega))
    (rlc_outerExitDart_isBoundary G omega)
    (iterate_isBoundaryDart'
      (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitDart G omega)
      (rlc_outerExitDart_isBoundary G omega) k)
    rfl


end Universality
end StatMech
