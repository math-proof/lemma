module
public import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
public import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
public import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part12
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


noncomputable def edgeCopySourcePairDataWitnessAt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (m : ↥G.edgeFinset → ℕ)
    (d : edgeCopySourcePairData G A B) :
    Finset (Sharpness.FluxEdgeCopy.Copy G m) := by
  classical
  by_cases h : d.1 = m
  · cases h
    exact d.2.1
  · exact ∅

end Exact3D
end StatMech
