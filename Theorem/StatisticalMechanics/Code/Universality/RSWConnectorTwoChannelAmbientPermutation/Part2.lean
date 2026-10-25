/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelAmbientPermutation
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_finiteExtremalPairCandidate_pairwiseDisjoint
    {n : Int} (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n) :
    Pairwise fun pair pair' : RlcDiagonalPathPair n ↦
      Disjoint
        (rlc_finiteExtremalPairCandidate pair.1 pair.2)
        (rlc_finiteExtremalPairCandidate pair'.1 pair'.2) := by
  intro pair pair' hne
  rw [Set.disjoint_left]
  intro psi hpair hpair'
  exact Set.disjoint_left.mp
    (rlc_extremalPairCandidate_pairwiseDisjoint hright hleft hne)
    hpair hpair'


theorem rlc_activeFiniteExtremalPairCandidate_pairwiseDisjoint
    {n : Int} (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n) :
    Pairwise fun pair pair' : RlcTwoChannelActiveFiniteExtremalPair n ↦
      Disjoint
        (rlc_finiteExtremalPairCandidate pair.1.1 pair.1.2)
        (rlc_finiteExtremalPairCandidate pair'.1.1 pair'.1.2) := by
  intro pair pair' hne
  apply rlc_finiteExtremalPairCandidate_pairwiseDisjoint hright hleft
  intro heq
  exact hne (Subtype.ext heq)


end
end StatMech.Universality
