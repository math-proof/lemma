module
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
public import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelAmbientPermutation.Part3
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelFiniteExtremalPairSelector
    {n : Int} (psi : RlcTwoChannelFiniteDiagonalConfig n) :
    RlcTwoChannelActiveFiniteExtremalPair n :=
  ⟨Classical.choose (rlc_exists_finiteExtremalPairCandidate psi),
    ⟨psi.1, Classical.choose_spec
      (rlc_exists_finiteExtremalPairCandidate psi)⟩⟩


end
end StatMech.Universality
