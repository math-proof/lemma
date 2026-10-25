/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part12
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem RlcTwoChannelCanonicalFibrePacking.embedding_compatible {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma'}
    (packing : RlcTwoChannelCanonicalFibrePacking target)
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    (rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible
      (rlc_twoChannelCanonicalRouteAvailable target) rho
        (packing.embedding rho) := by
  refine ⟨rlc_twoChannelCanonicalRoute (target rho), rfl, ?_⟩
  exact packing.pack_mem_codeSet rho


theorem RlcTwoChannelCanonicalFibrePacking.hasCodeHall {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma'}
    (packing : RlcTwoChannelCanonicalFibrePacking target) :
    (rlc_twoChannelCanonicalRoutePlan gamma gamma').HasCodeHall
      (rlc_twoChannelCanonicalRouteAvailable target) := by
  apply (rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding
    gamma gamma'
    ((rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible
      (rlc_twoChannelCanonicalRouteAvailable target))).mpr
  exact ⟨packing.embedding, packing.embedding_compatible⟩


theorem rlc_twoChannelCanonicalRoute_hasCodeHall_of_injective {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma')
    (htarget : Function.Injective target) :
    (rlc_twoChannelCanonicalRoutePlan gamma gamma').HasCodeHall
      (rlc_twoChannelCanonicalRouteAvailable target) := by
  apply (rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding
    gamma gamma'
    ((rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible
      (rlc_twoChannelCanonicalRouteAvailable target))).mpr
  exact ⟨⟨target, htarget⟩,
    rlc_twoChannelCanonicalRoute_target_compatible target⟩


end
end StatMech.Universality
