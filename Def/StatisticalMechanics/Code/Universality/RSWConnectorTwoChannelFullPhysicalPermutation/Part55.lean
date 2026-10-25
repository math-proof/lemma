/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part54
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_faceFlipXLatticeHom :
    hypercubicLattice 2 →g hypercubicLattice 2 where
  toFun := rlc_faceFlipX
  map_rel' := by
    intro f g hfg
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hfg ⊢
    change ((-f 0 - 1) - (-g 0 - 1)).natAbs +
      (f 1 - g 1).natAbs = 1
    rw [show (-f 0 - 1) - (-g 0 - 1) = -(f 0 - g 0) by ring,
      Int.natAbs_neg]
    exact hfg

end
end StatMech.Universality
