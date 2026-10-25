/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelVisibleFibreHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part43
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelVisibleFibreHall.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

noncomputable section

theorem rlc_twoChannelPooledVisibleEmbeddingOfCapacity_compatible
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure)
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    RlcTwoChannelPIMSPooledVisibleCompatible hclosure rho
      (rlc_twoChannelPooledVisibleEmbeddingOfCapacity hcapacity rho) := by
  have hbase :=
    (rlc_twoChannelVisibleFibreEmbedding hcapacity
      (rlc_twoChannelFailureVisibleBase hclosure rho)
      ⟨rho, rfl⟩).2
  simpa [RlcTwoChannelPIMSPooledVisibleCompatible,
    rlc_twoChannelPooledVisibleEmbeddingOfCapacity, rlc_sigmaEmbedding] using
      hbase


end
end StatMech.Universality
