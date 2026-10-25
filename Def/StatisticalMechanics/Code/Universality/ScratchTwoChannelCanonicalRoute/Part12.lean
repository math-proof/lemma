/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Structure.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def RlcTwoChannelCanonicalFibrePacking.embedding {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma'}
    (packing : RlcTwoChannelCanonicalFibrePacking target) :
    RlcTwoChannelEdgeFailure gamma gamma' ↪
      RlcTwoChannelEdgeSuccess gamma gamma' where
  toFun := packing.pack
  inj' := by
    intro rho sigma hpack
    have htarget : target rho = target sigma := calc
      target rho = packing.recoverBase (packing.pack rho) :=
        (packing.recoverBase_pack rho).symm
      _ = packing.recoverBase (packing.pack sigma) :=
        congrArg packing.recoverBase hpack
      _ = target sigma := packing.recoverBase_pack sigma
    exact packing.pack_injective_on_fibre rho sigma htarget hpack

end
end StatMech.Universality
