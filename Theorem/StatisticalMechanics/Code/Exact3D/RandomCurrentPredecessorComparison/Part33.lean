module
public import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
public import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
public import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part31
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

theorem doubledBoxOriginToInnerEndpointSelectedCopySplitBound_eq_beta_mul_sourcePairSplitScalar
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n) :
    doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w =
      β * doubledBoxOriginToInnerEndpointSourcePairSplitScalar β n v w := by
  rfl

end Exact3D
end StatMech
