module
public import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
public import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
public import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part14
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


noncomputable def edgeCopySourcePairData_empty_of_fullSource
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ)
    (hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A) :
    edgeCopySourcePairData G A (∅ : Finset V) :=
  ⟨m, ⟨Finset.univ, hfull, by
    simpa using randomCurrent_sources_empty (Sharpness.FluxEdgeCopy.endsM G m)⟩⟩

end Exact3D
end StatMech
