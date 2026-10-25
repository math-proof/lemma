/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part11
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_flipXLatticeHom :
    hypercubicLattice 2 →g hypercubicLattice 2 where
  toFun := rlc_flipXFun
  map_rel' := by
    intro x y hxy
    change (x 0 - y 0).natAbs + (x 1 - y 1).natAbs = 1 at hxy
    change (-x 0 - -y 0).natAbs + (x 1 - y 1).natAbs = 1
    have h0 : (-x 0 - -y 0).natAbs = (x 0 - y 0).natAbs := by
      rw [show -x 0 - -y 0 = -(x 0 - y 0) by ring, Int.natAbs_neg]
    rw [h0]
    exact hxy

end
end StatMech.Universality
