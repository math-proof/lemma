/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCyclicLocalPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexEndpointLocalPartitionClosure


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

noncomputable section

inductive HexEndpointCyclicLocalAtom (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) where
  | triplet : HexEndpointCyclicTriplet region a h0 v du →
      HexEndpointCyclicLocalAtom region a h0 v du
  | pair : HexEndpointCyclicLoopPair region a h0 v du →
      HexEndpointCyclicLocalAtom region a h0 v du

end
end StatMech.Universality
