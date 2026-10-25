/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part9
import Abbrev.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelEdgeEncoding
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelConfigSplitEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) ≃
      RlcTwoChannelEdgeConfig gamma gamma' ×
        RlcTwoChannelOffGraphConfig gamma gamma' where
  toFun rho :=
    (fun e => rho e.1, fun e => rho e.1)
  invFun pair e := if he : e ∈
      (rlc_connectorTwoChannelGraph gamma gamma').edgeSet then
    pair.1 ⟨e, he⟩
  else
    pair.2 ⟨e, he⟩
  left_inv rho := by
    funext e
    by_cases he : e ∈
        (rlc_connectorTwoChannelGraph gamma gamma').edgeSet <;>
      simp [he]
  right_inv pair := by
    apply Prod.ext
    · funext e
      simp [e.2]
    · funext e
      simp [e.2]


noncomputable def rlc_twoChannelEdgeConfigExtend {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  (rlc_twoChannelConfigSplitEquiv gamma gamma').symm
    (omega, fun _ => false)


noncomputable def rlc_twoChannelEdgeConfigCombine {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (outside : RlcTwoChannelOffGraphConfig gamma gamma') :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  (rlc_twoChannelConfigSplitEquiv gamma gamma').symm (omega, outside)

end
end StatMech.Universality
