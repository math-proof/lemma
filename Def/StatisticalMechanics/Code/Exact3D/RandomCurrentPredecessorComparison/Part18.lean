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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part18
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0) :
    edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
  let G := FK.boxGraph 3 (2 * n)
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n w)
      (m := m) (e0 := e0) p).mp hp
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n w)
      (m := m) (e0 := e0) p).mp hpbranch.1
  have hsrc :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) p.1 =
        doubledBoxOriginToInnerEndpointSource n w := by
    exact
      (mem_edgeCopySourceSector
        (G := FK.boxGraph 3 (2 * n))
        (A := doubledBoxOriginToInnerEndpointSource n w)
        (m := m)).mp hpbase.1
  have hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m p.2 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) := by
    simpa [G, Sharpness.FluxEdgeCopy.endsM, hpbase.2] using hedge
  refine
    ⟨Function.update m p.2.1 (m p.2.1 - 1),
      ⟨copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m p.2 p.1,
        ⟨?_, ?_⟩⟩⟩
  · exact
      doubledBox_sources_preimageErase_innerPairCopy
        (n := n) (v := v) (w := w) m p.1 hpbranch.2 hsrc hends
        hov how hvw
  · exact
      doubledBox_sources_complement_preimageErase_innerPairCopy
        (n := n) (v := v) (w := w) m p.1 hpbranch.2 hsrc hfull hends
        hov how hvw

set_option linter.style.longLine false in


noncomputable def doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0) :
    edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) := by
  let G := FK.boxGraph 3 (2 * n)
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n w)
      (m := m) (e0 := e0) p).mp hp
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n w)
      (m := m) (e0 := e0) p).mp hpbranch.1
  have hsrc :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) p.1 =
        doubledBoxOriginToInnerEndpointSource n w := by
    exact
      (mem_edgeCopySourceSector
        (G := FK.boxGraph 3 (2 * n))
        (A := doubledBoxOriginToInnerEndpointSource n w)
        (m := m)).mp hpbase.1
  have hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m p.2 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) := by
    simpa [G, Sharpness.FluxEdgeCopy.endsM, hpbase.2] using hedge
  refine
    ⟨Function.update m p.2.1 (m p.2.1 - 1),
      ⟨copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m p.2 p.1,
        ⟨?_, ?_⟩⟩⟩
  · exact
      doubledBox_sources_preimageErase_of_not_mem
        (n := n) (w := w) m p.1 hpbranch.2 hsrc
  · exact
      doubledBox_sources_complement_preimageErase_of_not_mem_innerPairCopy
        (n := n) (v := v) (w := w) m p.1 hpbranch.2 hsrc hfull hends
        hov how hvw

set_option linter.style.longLine false in


noncomputable def
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m e0) :
    edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
  let G := FK.boxGraph 3 (2 * n)
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n v)
      (m := m) (e0 := e0) p).mp hp
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n v)
      (m := m) (e0 := e0) p).mp hpbranch.1
  have hsrc :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) p.1 =
        doubledBoxOriginToInnerEndpointSource n v := by
    exact
      (mem_edgeCopySourceSector
        (G := FK.boxGraph 3 (2 * n))
        (A := doubledBoxOriginToInnerEndpointSource n v)
        (m := m)).mp hpbase.1
  have hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m p.2 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) := by
    simpa [G, Sharpness.FluxEdgeCopy.endsM, hpbase.2] using hedge
  refine
    ⟨Function.update m p.2.1 (m p.2.1 - 1),
      ⟨copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m p.2 p.1,
        ⟨?_, ?_⟩⟩⟩
  · exact
      doubledBox_sources_preimageErase_of_not_mem
        (n := n) (w := v) m p.1 hpbranch.2 hsrc
  · exact
      doubledBox_sources_complement_preimageErase_of_not_mem_switched_empty
        (n := n) (v := v) (w := w) m p.1 hpbranch.2 hsrc hfull
        hends hov how hvw

set_option linter.style.longLine false in


noncomputable def
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairData
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v w) m e0) :
    edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
      (doubledBoxInnerPairSource n v w)
      (doubledBoxOriginToInnerEndpointSource n w) := by
  let G := FK.boxGraph 3 (2 * n)
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      (G := G) (A := doubledBoxInnerPairSource n v w)
      (m := m) (e0 := e0) p).mp hp
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (G := G) (A := doubledBoxInnerPairSource n v w)
      (m := m) (e0 := e0) p).mp hpbranch.1
  have hsrc :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) p.1 =
        doubledBoxInnerPairSource n v w := by
    exact
      (mem_edgeCopySourceSector
        (G := FK.boxGraph 3 (2 * n))
        (A := doubledBoxInnerPairSource n v w)
        (m := m)).mp hpbase.1
  have hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m p.2 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) := by
    simpa [G, Sharpness.FluxEdgeCopy.endsM, hpbase.2] using hedge
  refine
    ⟨Function.update m p.2.1 (m p.2.1 - 1),
      ⟨copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m p.2 p.1,
        ⟨?_, ?_⟩⟩⟩
  · exact
      (copyDeletePreimageDecrementErase_sources_of_not_mem
        (G := FK.boxGraph 3 (2 * n)) m p.1 hpbranch.2).trans hsrc
  · exact
      doubledBox_sources_complement_preimageErase_of_not_mem_innerPairSource
        (n := n) (v := v) (w := w) m p.1 hpbranch.2 hsrc hfull
        hends hov how hvw

set_option linter.style.longLine false in


noncomputable def
    doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m e0) :
    edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) := by
  let G := FK.boxGraph 3 (2 * n)
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n v)
      (m := m) (e0 := e0) p).mp hp
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n v)
      (m := m) (e0 := e0) p).mp hpbranch.1
  have hsrc :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) p.1 =
        doubledBoxOriginToInnerEndpointSource n v := by
    exact
      (mem_edgeCopySourceSector
        (G := FK.boxGraph 3 (2 * n))
        (A := doubledBoxOriginToInnerEndpointSource n v)
        (m := m)).mp hpbase.1
  have hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m p.2 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) := by
    simpa [G, Sharpness.FluxEdgeCopy.endsM, hpbase.2] using hedge
  refine
    ⟨Function.update m p.2.1 (m p.2.1 - 1),
      ⟨copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m p.2 p.1,
        ⟨?_, ?_⟩⟩⟩
  · exact
      doubledBox_sources_preimageErase_innerPairCopy_switched
        (n := n) (v := v) (w := w) m p.1 hpbranch.2 hsrc hends
        hov how hvw
  · exact
      doubledBox_sources_complement_preimageErase_innerPairCopy_switched_innerPair
        (n := n) (v := v) (w := w) m p.1 hpbranch.2 hsrc hfull
        hends hov how hvw

end Exact3D
end StatMech
