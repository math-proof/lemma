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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part16
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

noncomputable def edgeCopySourceSectorSelectedEdgeCopyPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    Finset (Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
      Sharpness.FluxEdgeCopy.Copy G m)) :=
  (edgeCopySourceSector G A m).sigma (fun _K =>
    edgeCopyCopiesOfEdge G m e0)


end Exact3D
end StatMech
