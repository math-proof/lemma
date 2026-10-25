/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelAmbientPermutation.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFiniteExtremalPairSelector_selected
    {n : Int} (psi : RlcTwoChannelFiniteDiagonalConfig n) :
    psi.1 ∈ rlc_finiteExtremalPairCandidate
      (rlc_twoChannelFiniteExtremalPairSelector psi).1.1
      (rlc_twoChannelFiniteExtremalPairSelector psi).1.2 := by
  exact Classical.choose_spec (rlc_exists_finiteExtremalPairCandidate psi)


theorem rlc_twoChannelFiniteExtremalPairSelector_eq_of_selected
    {n : Int} (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n)
    (psi : RlcTwoChannelFiniteDiagonalConfig n)
    (pair : RlcTwoChannelActiveFiniteExtremalPair n)
    (hselected : psi.1 ∈
      rlc_finiteExtremalPairCandidate pair.1.1 pair.1.2) :
    rlc_twoChannelFiniteExtremalPairSelector psi = pair := by
  by_contra hne
  exact Set.disjoint_left.mp
    (rlc_activeFiniteExtremalPairCandidate_pairwiseDisjoint
      hright hleft hne)
    (rlc_twoChannelFiniteExtremalPairSelector_selected psi) hselected


end
end StatMech.Universality
