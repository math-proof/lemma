/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable instance rlc_twoChannelIndexedOuterVertexFintype {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Fintype (RlcTwoChannelIndexedOuterVertex gamma gamma') := by
  letI : Fintype (Ising.kwg_Face
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :=
    Fintype.ofFinite _
  infer_instance

noncomputable instance rlc_twoChannelIndexedOuterVertexDecidableEq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableEq (RlcTwoChannelIndexedOuterVertex gamma gamma') :=
  Classical.decEq _

end
end StatMech.Universality
