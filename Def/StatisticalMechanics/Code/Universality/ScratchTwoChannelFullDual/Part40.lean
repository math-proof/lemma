/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part31
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def rlc_twoChannelFullRightInnerAnchor {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelFullInnerVertex gamma gamma' :=
  ⟨rlc_connectorRightAnchor gamma, Or.inl rfl⟩


noncomputable def rlc_twoChannelFullMaxComponentTraceRep {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelFullMaxOutsideComponent gamma gamma' →
      RlcConnectorVertex n := by
  classical
  exact fun C => if C = rlc_twoChannelFullMaxInnerContraction gamma gamma'
        (rlc_twoChannelFullRightInnerAnchor gamma gamma') then
      rlc_connectorRightAnchor gamma
    else rlc_connectorLeftAnchor gamma'

end
end StatMech.Universality
