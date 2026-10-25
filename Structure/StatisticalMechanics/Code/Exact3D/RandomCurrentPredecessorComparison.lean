/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part21
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

structure EdgeCopySourceSectorInjection
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (m m' : ↥G.edgeFinset → ℕ) where
  fullSource :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A →
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m')
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) = B
  toFun :
    (K : Finset (Sharpness.FluxEdgeCopy.Copy G m)) →
      K ∈ edgeCopySourceSector G A m →
        Finset (Sharpness.FluxEdgeCopy.Copy G m')
  map_mem :
    ∀ K hK, toFun K hK ∈ edgeCopySourceSector G B m'
  injective :
    ∀ K₁ hK₁ K₂ hK₂,
      toFun K₁ hK₁ = toFun K₂ hK₂ → K₁ = K₂


structure EdgeCopySourceSectorImageEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (m m' : ↥G.edgeFinset → ℕ) where
  copyMap :
    Sharpness.FluxEdgeCopy.Copy G m → Sharpness.FluxEdgeCopy.Copy G m'
  copyMap_injective : Function.Injective copyMap
  fullSource :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A →
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m')
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) = B
  sources_image :
    ∀ K : Finset (Sharpness.FluxEdgeCopy.Copy G m),
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m) K = A →
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m')
          (K.image copyMap) = B


structure EdgeCopySourceSectorInsertEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (m m' : ↥G.edgeFinset → ℕ) where
  copyMap :
    Sharpness.FluxEdgeCopy.Copy G m → Sharpness.FluxEdgeCopy.Copy G m'
  copyMap_injective : Function.Injective copyMap
  inserted : Sharpness.FluxEdgeCopy.Copy G m'
  inserted_not_mem_image : ∀ i, copyMap i ≠ inserted
  fullSource :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A →
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m')
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) = B
  sources_insert :
    ∀ K : Finset (Sharpness.FluxEdgeCopy.Copy G m),
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m) K = A →
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m')
          (insert inserted (K.image copyMap)) = B


end Exact3D
end StatMech
