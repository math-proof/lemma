/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCyclicLocalPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexEndpointLocalPartitionClosure
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCyclicLocalPartition


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

noncomputable section

structure HexEndpointCyclicLocalPartition
    (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ) (v du : ℂ) where
  atoms : Finset (HexEndpointCyclicLocalAtom R.inRegion a h0 v du)
  cover : atoms.biUnion HexEndpointCyclicLocalAtom.piece =
    R.endpointCombinedSupportFinset a h0 v du
  disjoint :
    (↑atoms : Set (HexEndpointCyclicLocalAtom R.inRegion a h0 v du)).PairwiseDisjoint
      HexEndpointCyclicLocalAtom.piece


end
end StatMech.Universality
