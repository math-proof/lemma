module
public import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
public import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
public import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part9
open scoped BigOperators symmDiff
open MeasureTheory
set_option linter.style.longLine false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem edgeCopySourcePairWitnesses_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (m : ↥G.edgeFinset → ℕ)
    (S : Finset (Sharpness.FluxEdgeCopy.Copy G m)) :
    S ∈ edgeCopySourcePairWitnesses G A B m ↔
      Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m) S = A ∧
      Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m)
        ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ S) = B := by
  simp [edgeCopySourcePairWitnesses]

end Exact3D
end StatMech
