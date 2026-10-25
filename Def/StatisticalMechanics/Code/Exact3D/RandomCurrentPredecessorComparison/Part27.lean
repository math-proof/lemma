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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part28
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

noncomputable def EdgeCopySourceSectorImageEmbedding.ofEdgeEquivVertexEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (φ : V ≃ V)
    (σ : ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hm : ∀ e, m' (σ e) = m e)
    (hends : ∀ e, (σ e).1 = Sym2.map φ e.1)
    (hAB : A.map φ.toEmbedding = B) :
    EdgeCopySourceSectorImageEmbedding G A B m m' :=
  EdgeCopySourceSectorImageEmbedding.ofVertexEquiv φ
    (edgeCopyEquivOfEdgeEquiv G σ hm)
    (edgeCopyEquivOfEdgeEquiv_ends φ σ hm hends)
    hAB


end Exact3D
end StatMech
