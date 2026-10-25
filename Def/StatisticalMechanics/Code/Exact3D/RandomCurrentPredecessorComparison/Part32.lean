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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part33
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairDataImage
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    Finset (edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n)))) :=
  (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) m e0).attach.image
    (fun p =>
      doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw
        (p := p.1) p.2)

set_option linter.style.longLine false in


noncomputable def doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairDataImage
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    Finset (edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w)) :=
  (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) m e0).attach.image
    (fun p =>
      doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw
        (p := p.1) p.2)

set_option linter.style.longLine false in


noncomputable def
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairDataImage
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    Finset (edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n)))) :=
  (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v) m e0).attach.image
    (fun p =>
      doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw
        (p := p.1) p.2)

set_option linter.style.longLine false in


noncomputable def
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairDataImage
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    Finset (edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
      (doubledBoxInnerPairSource n v w)
      (doubledBoxOriginToInnerEndpointSource n w)) :=
  (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxInnerPairSource n v w) m e0).attach.image
    (fun p =>
      doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairData
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw
        (p := p.1) p.2)

set_option linter.style.longLine false in


noncomputable def
    doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairDataImage
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    Finset (edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w)) :=
  (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v) m e0).attach.image
    (fun p =>
      doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw
        (p := p.1) p.2)

end Exact3D
end StatMech
