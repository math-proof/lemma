/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronNoAdjacent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPerronNoAdjacent
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHalfFilledTransferInfinityVector_eigenrelation
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N) :
    sixVertexSectorTransferInfinity N n *ᵥ
        sixVertexHalfFilledTransferInfinityVector N n hhalf =
      sixVertexHalfFilledTransferInfinityVector N n hhalf := by
  classical
  let even := sixVertexAlternatingEvenSector N n hhalf.le
  let odd := sixVertexAlternatingOddSector N n hhalf.le
  have hne : even ≠ odd :=
    (sixVertexInfinityGraph_adj_alternating_of_half hn hhalf).ne
  funext x
  rw [Matrix.mulVec, dotProduct]
  by_cases hxe : x = even
  · subst x
    rw [Fintype.sum_eq_single odd]
    · simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
        sixVertexHalfFilledTransferInfinityVector, even, odd, hne]
    · intro y hy
      simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
        sixVertexHalfFilledTransferInfinityVector, even, odd, hne, hy]
  by_cases hxo : x = odd
  · subst x
    rw [Fintype.sum_eq_single even]
    · simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
        sixVertexHalfFilledTransferInfinityVector, even, odd, hne,
        Ne.symm hne]
    · intro y hy
      simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
        sixVertexHalfFilledTransferInfinityVector, even, odd, hne,
        Ne.symm hne, hy]
  · simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
      sixVertexHalfFilledTransferInfinityVector, even, odd, hxe, hxo]


theorem sixVertexSectorTransferInfinity_eigenvector_one_eq_smul
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N)
    (v : SixVertexSector N n → Real)
    (hv : sixVertexSectorTransferInfinity N n *ᵥ v = v) :
    v = v (sixVertexAlternatingEvenSector N n hhalf.le) •
      sixVertexHalfFilledTransferInfinityVector N n hhalf := by
  let even := sixVertexAlternatingEvenSector N n hhalf.le
  let odd := sixVertexAlternatingOddSector N n hhalf.le
  have hne : even ≠ odd :=
    (sixVertexInfinityGraph_adj_alternating_of_half hn hhalf).ne
  funext x
  have hx := congrFun hv x
  rw [sixVertexSectorTransferInfinity_mulVec_half hn hhalf] at hx
  by_cases hxe : x = even
  · subst x
    simp [sixVertexHalfFilledTransferInfinityVector, even, odd]
  · by_cases hxo : x = odd
    · subst x
      simpa [sixVertexHalfFilledTransferInfinityVector, even, odd,
        hne, Ne.symm hne] using hx.symm
    · simpa [sixVertexHalfFilledTransferInfinityVector, even, odd,
        hxe, hxo] using hx.symm

end
end StatMech.FrontierD
