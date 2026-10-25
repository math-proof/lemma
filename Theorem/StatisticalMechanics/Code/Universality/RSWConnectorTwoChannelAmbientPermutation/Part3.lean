/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
import Abbrev.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelAmbientPermutation.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_exists_finiteExtremalPairCandidate
    {n : Int} (psi : RlcTwoChannelFiniteDiagonalConfig n) :
    ∃ pair : RlcDiagonalPathPair n,
      psi.1 ∈ rlc_finiteExtremalPairCandidate pair.1 pair.2 := by
  have h : rlc_connectorExtendConfig psi.1 ∈
      ⋃ pair : RlcDiagonalPathPair n, rlc_extremalPairCandidate pair := by
    rw [rlc_iUnion_extremalPairCandidate n]
    exact psi.2
  obtain ⟨pair, hpair⟩ := Set.mem_iUnion.mp h
  exact ⟨pair, hpair⟩

end
end StatMech.Universality
