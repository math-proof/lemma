/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part13


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

structure HexEndpointLocalPartition (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) where
  atoms : Finset (HexEndpointLocalAtom R.inRegion a h0 v du)
  cover : atoms.biUnion HexEndpointLocalAtom.piece =
    R.endpointCombinedSupportFinset a h0 v du
  disjoint : (↑atoms : Set (HexEndpointLocalAtom R.inRegion a h0 v du)).PairwiseDisjoint
    HexEndpointLocalAtom.piece


end
end StatMech.Universality
