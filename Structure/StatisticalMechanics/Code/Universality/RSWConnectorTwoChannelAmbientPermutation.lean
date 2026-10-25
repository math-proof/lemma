/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelAmbientPermutation.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

structure RlcTwoChannelIndexedSelectedFailure {n : Int} (I : Type*)
    (pair : I → RlcDiagonalPathPair n) where
  index : I
  config : ConfigSpace (Sym2 (RlcConnectorVertex n))
  selected : config ∈
    rlc_finiteExtremalPairCandidate (pair index).1 (pair index).2
  failure : config ∉
    rlc_finiteTwoChannelConnectorEvent (pair index).1 (pair index).2


end
end StatMech.Universality
