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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part27
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def EdgeCopySourceSectorInsertEmbedding.doubledBoxOriginToInnerEndpoint_edgeIncrement_of_orderedWedge_lowerDoubledAdj
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)) :
    Σ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
      EdgeCopySourceSectorInsertEmbedding (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (doubledBoxOriginToInnerEndpointSource n w) m
        (Function.update m e0 (m e0 + 1)) := by
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨e0, hedge, hov, how, hvw⟩
  exact
    ⟨e0,
      EdgeCopySourceSectorInsertEmbedding.doubledBoxOriginToInnerEndpoint_edgeIncrement
        (n := n) (v := v) (w := w) m e0 hedge hov how hvw⟩


noncomputable def EdgeCopySourceSectorInsertEmbedding.doubledBoxOriginToInnerEndpoint_univ
    {n : ℕ} {v w : FK.boxVerts 3 n}
    {m m' : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (copyMap :
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m →
        Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m')
    (hcopy : Function.Injective copyMap)
    (inserted :
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m')
    (hdisjoint : ∀ i, copyMap i ≠ inserted)
    (hends :
      ∀ i,
        Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m'
            (copyMap i) =
          Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i)
    (hinserted :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m'
          inserted =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (huniv :
      insert inserted
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) m)).image copyMap) =
        (Finset.univ :
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m'))) :
    EdgeCopySourceSectorInsertEmbedding (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (doubledBoxOriginToInnerEndpointSource n w) m m' :=
  EdgeCopySourceSectorInsertEmbedding.ofEndpointPreservingInsertedPair_univ
    (G := FK.boxGraph 3 (2 * n))
    (A := doubledBoxOriginToInnerEndpointSource n v)
    (B := doubledBoxOriginToInnerEndpointSource n w)
    (m := m) (m' := m')
    copyMap hcopy inserted hdisjoint hends hinserted
    (doubledBoxOriginToInnerEndpointSource_symmDiff_innerPair_eq
      (n := n) (v := v) (w := w) hov how hvw)
    huniv


noncomputable def edgeCopyEquivOfEdgeEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m m' : ↥G.edgeFinset → ℕ}
    (σ : ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hm : ∀ e, m' (σ e) = m e) :
    Sharpness.FluxEdgeCopy.Copy G m ≃
      Sharpness.FluxEdgeCopy.Copy G m' :=
  Equiv.sigmaCongr σ fun e => finCongr (hm e).symm


end Exact3D
end StatMech
