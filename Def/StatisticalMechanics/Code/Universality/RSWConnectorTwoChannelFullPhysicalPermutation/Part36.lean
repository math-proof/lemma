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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part35
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_dualReflectSymmLatticeHom :
    hypercubicLattice 2 →g hypercubicLattice 2 where
  toFun := rlc_dualReflect.symm
  map_rel' := by
    intro x y hxy
    apply (rlc_adj_dualReflect
      (rlc_dualReflect.symm x) (rlc_dualReflect.symm y)).mpr
    simpa using hxy


noncomputable def rlc_doubleDualShiftLatticeHom :
    hypercubicLattice 2 →g hypercubicLattice 2 where
  toFun := phb_doubleDualShift
  map_rel' := fun {_ _} h => phb_doubleDualShift_latAdj.mpr h


noncomputable def rlc_doubleDualShiftSymmLatticeHom :
    hypercubicLattice 2 →g hypercubicLattice 2 where
  toFun := phb_doubleDualEquiv.symm
  map_rel' := by
    intro x y hxy
    apply phb_doubleDualShift_latAdj.mp
    simpa [phb_doubleDualEquiv, phb_doubleDualShift] using hxy


end
end StatMech.Universality
