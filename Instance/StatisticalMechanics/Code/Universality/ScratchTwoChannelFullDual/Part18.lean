module
public import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
public import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
public import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part51
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable instance rlc_twoChannelFaithfulFaceSeparateWiringDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel
      (rlc_twoChannelFaithfulFaceSeparateWiring gamma gamma').Adj :=
  Classical.decRel _

noncomputable instance rlc_twoChannelFaithfulFaceMergedWiringDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel
      (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma').Adj :=
  Classical.decRel _

end
end StatMech.Universality
