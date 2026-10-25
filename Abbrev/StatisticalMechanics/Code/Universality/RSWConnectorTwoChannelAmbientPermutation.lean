/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelAmbientPermutation
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

abbrev RlcTwoChannelActiveFiniteExtremalPair (n : Int) :=
  {pair : RlcDiagonalPathPair n //
    (rlc_finiteExtremalPairCandidate pair.1 pair.2).Nonempty}

end
end StatMech.Universality
