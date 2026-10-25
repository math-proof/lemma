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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part9
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

noncomputable def edgeCopySourcePairWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (m : ↥G.edgeFinset → ℕ) :
    Finset (Finset (Sharpness.FluxEdgeCopy.Copy G m)) :=
  (Finset.univ : Finset (Finset (Sharpness.FluxEdgeCopy.Copy G m))).filter
    (fun S =>
      Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m) S = A ∧
        Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m)
          ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ S) = B)

end Exact3D
end StatMech
