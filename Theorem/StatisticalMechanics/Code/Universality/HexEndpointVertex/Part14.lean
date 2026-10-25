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
import Structure.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part4


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

theorem HexEndpointLocalPartition.vertex_relation
    {R : HexFiniteRegion} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (P : HexEndpointLocalPartition R a h0 v du) :
    ((v + du) - v) *
        endpointParafObservable R.inRegion a h0 (v + du)
          (5 / 8) hexChi +
      ((v + hexOmega * du) - v) *
        endpointParafObservable R.inRegion a h0 (v + hexOmega * du)
          (5 / 8) hexChi +
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi = 0 := by
  rw [endpointVertexSum_eq_tsum_combined]
  rw [tsum_eq_sum (s := R.endpointCombinedSupportFinset a h0 v du)]
  · rw [← P.cover, Finset.sum_biUnion P.disjoint]
    exact Finset.sum_eq_zero fun A _ => A.sum_piece_zero hdu
  · intro ts hts
    by_contra hne
    exact hts ((R.mem_endpointCombinedSupportFinset a h0 v du ts).2 hne)

end
end StatMech.Universality
