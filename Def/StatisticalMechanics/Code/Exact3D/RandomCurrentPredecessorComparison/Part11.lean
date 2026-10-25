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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part11
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def edgeCopySourcePairData_swap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (d : edgeCopySourcePairData G A B) :
    edgeCopySourcePairData G B A := by
  rcases d with ⟨m, K, hK⟩
  exact
    ⟨m,
      ⟨(Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ K,
        ⟨hK.2, by
          simpa using hK.1⟩⟩⟩

end Exact3D
end StatMech
