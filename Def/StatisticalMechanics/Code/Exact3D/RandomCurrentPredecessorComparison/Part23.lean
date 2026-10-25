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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part24
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

noncomputable def EdgeCopySourceSectorInsertEmbedding.ofEdgeIncrementEndpointPair
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    {a b : V}
    (hedge : e0.1 = s(a, b))
    (hAB : A ∆ ({a, b} : Finset V) = B) :
    EdgeCopySourceSectorInsertEmbedding G A B m
      (Function.update m e0 (m e0 + 1)) :=
  EdgeCopySourceSectorInsertEmbedding.ofEndpointPreservingInsertedPair_univ
    (G := G) (A := A) (B := B)
    (m := m) (m' := Function.update m e0 (m e0 + 1))
    (edgeCopyIncrementMap G m e0)
    (edgeCopyIncrementMap_injective G m e0)
    (edgeCopyIncrementInserted G m e0)
    (edgeCopyIncrementMap_ne_inserted G m e0)
    (edgeCopyIncrementMap_ends G m e0)
    (by simpa [edgeCopyIncrementInserted_ends G m e0] using hedge)
    hAB
    (edgeCopyIncrement_univ G m e0)

end Exact3D
end StatMech
