module
public import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
public import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
public import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part77
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


abbrev doubledBoxIncrementedFullSourceActive
    (n : ℕ) (w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) : Prop :=
  Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)))
      (Finset.univ :
        Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
          (Function.update m e0 (m e0 + 1)))) =
    doubledBoxOriginToInnerEndpointSource n w

end Exact3D
end StatMech
