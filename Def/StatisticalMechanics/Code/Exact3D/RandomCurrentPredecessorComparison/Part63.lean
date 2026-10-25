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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part69
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in Filter.atTop,
      Nonempty
        (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage
          n)


end Exact3D
end StatMech
