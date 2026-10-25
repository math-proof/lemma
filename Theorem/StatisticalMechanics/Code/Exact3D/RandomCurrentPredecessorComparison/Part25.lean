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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part23
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem edgeCopySourceSector_card_le_containing_incrementInserted_card_of_edgeIncrementEndpointPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    {a b : V}
    (hedge : e0.1 = s(a, b))
    (hAB : A ∆ ({a, b} : Finset V) = B) :
    (edgeCopySourceSector G A m).card ≤
      (edgeCopySourceSectorContainingCopy G B
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0)).card := by
  let I :=
    EdgeCopySourceSectorInsertEmbedding.ofEdgeIncrementEndpointPair
      (G := G) (A := A) (B := B) m e0 hedge hAB
  simpa [I] using
    edgeCopySourceSector_card_le_containingCopy_card_of_insertEmbedding G I

set_option linter.style.longLine false in

theorem edgeCopySourceSectorContaining_incrementInserted_card_pos_of_sourceSector_card_pos_edgeIncrementEndpointPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    {a b : V}
    (hedge : e0.1 = s(a, b))
    (hAB : A ∆ ({a, b} : Finset V) = B)
    (hpos : 0 < (edgeCopySourceSector G A m).card) :
    0 <
      (edgeCopySourceSectorContainingCopy G B
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted G m e0)).card :=
  lt_of_lt_of_le hpos
    (edgeCopySourceSector_card_le_containing_incrementInserted_card_of_edgeIncrementEndpointPair
      G m e0 hedge hAB)


end Exact3D
end StatMech
