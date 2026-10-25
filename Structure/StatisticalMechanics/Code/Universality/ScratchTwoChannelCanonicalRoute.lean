/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

structure RlcTwoChannelCanonicalFibrePacking {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma') where
  recoverBase : RlcTwoChannelEdgeSuccess gamma gamma' →
    RlcTwoChannelEdgeSuccess gamma gamma'
  pack : RlcTwoChannelEdgeFailure gamma gamma' →
    RlcTwoChannelEdgeSuccess gamma gamma'
  recoverBase_pack : ∀ rho, recoverBase (pack rho) = target rho
  pack_injective_on_fibre : ∀ rho sigma,
    target rho = target sigma → pack rho = pack sigma → rho = sigma
  pack_mem_codeSet : ∀ rho,
    (pack rho).1 ∈
      (rlc_twoChannelCanonicalRoutePlan gamma gamma').codeSet
        (rlc_twoChannelCanonicalRoute (target rho))


end
end StatMech.Universality
