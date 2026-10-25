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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part17
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

noncomputable def edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    Finset (Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
      Sharpness.FluxEdgeCopy.Copy G m)) :=
  (edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0).filter
    (fun p => p.2 ∈ p.1)


noncomputable def edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    Finset (Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
      Sharpness.FluxEdgeCopy.Copy G m)) :=
  (edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0).filter
    (fun p => p.2 ∉ p.1)


end Exact3D
end StatMech
