/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCyclicLocalPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexEndpointLocalPartitionClosure
import Def.StatisticalMechanics.Code.Universality.HexEndpointCyclicLocalPartition


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

noncomputable section

theorem HexEndpointCyclicLocalAtom.sum_piece_zero
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (A : HexEndpointCyclicLocalAtom region a h0 v du) :
    ∑ ts ∈ A.piece, endpointCombinedSummand region a h0 v du ts = 0 := by
  cases A with
  | triplet C => exact C.sum_piece_zero hdu
  | pair P => exact P.sum_piece_zero hdu


end
end StatMech.Universality
