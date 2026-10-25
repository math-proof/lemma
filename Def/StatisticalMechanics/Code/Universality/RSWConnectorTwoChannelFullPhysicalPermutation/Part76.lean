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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part76
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_walkIndexInterval
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (W : G.Walk a b) (i j : Nat)
    (hi : i ≤ W.length) (hij : i ≤ j) (hj : j ≤ W.length) :
    G.Walk (W.getVert i) (W.getVert j) :=
  ((W.drop i).take (j - i)).copy
    (by simp)
    (by
      rw [SimpleGraph.Walk.drop_getVert]
      congr 1
      omega)


end
end StatMech.Universality
