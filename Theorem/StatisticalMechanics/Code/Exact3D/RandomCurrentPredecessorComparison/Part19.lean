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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part18
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_decrementWitness_mem
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
    copyDeletePreimageDecrementEraseFinset
        (FK.boxGraph 3 (2 * n)) m p.2 p.1 ∈
      edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n)))
        (Function.update m p.2.1 (m p.2.1 - 1)) := by
  let d :=
    doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
  change d.2.1 ∈ edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
    (doubledBoxOriginToInnerEndpointSource n v)
    (∅ : Finset (FK.boxVerts 3 (2 * n))) d.1
  exact edgeCopySourcePairData_mem_witnesses (FK.boxGraph 3 (2 * n)) d

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementWitness_mem
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
    copyDeletePreimageDecrementEraseFinset
        (FK.boxGraph 3 (2 * n)) m p.2 p.1 ∈
      edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)
        (Function.update m p.2.1 (m p.2.1 - 1)) := by
  let d :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
  change d.2.1 ∈ edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
    (doubledBoxOriginToInnerEndpointSource n w)
    (doubledBoxInnerPairSource n v w) d.1
  exact edgeCopySourcePairData_mem_witnesses (FK.boxGraph 3 (2 * n)) d

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementWitness_mem
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
    copyDeletePreimageDecrementEraseFinset
        (FK.boxGraph 3 (2 * n)) m p.2 p.1 ∈
      edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n)))
        (Function.update m p.2.1 (m p.2.1 - 1)) := by
  let d :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
  change d.2.1 ∈ edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
    (doubledBoxOriginToInnerEndpointSource n v)
    (∅ : Finset (FK.boxVerts 3 (2 * n))) d.1
  exact edgeCopySourcePairData_mem_witnesses (FK.boxGraph 3 (2 * n)) d

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementWitness_mem
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
    copyDeletePreimageDecrementEraseFinset
        (FK.boxGraph 3 (2 * n)) m p.2 p.1 ∈
      edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v w)
        (doubledBoxOriginToInnerEndpointSource n w)
        (Function.update m p.2.1 (m p.2.1 - 1)) := by
  let d :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairData
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
  change d.2.1 ∈ edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
    (doubledBoxInnerPairSource n v w)
    (doubledBoxOriginToInnerEndpointSource n w) d.1
  exact edgeCopySourcePairData_mem_witnesses (FK.boxGraph 3 (2 * n)) d

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementWitness_mem
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
    copyDeletePreimageDecrementEraseFinset
        (FK.boxGraph 3 (2 * n)) m p.2 p.1 ∈
      edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)
        (Function.update m p.2.1 (m p.2.1 - 1)) := by
  let d :=
    doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
  change d.2.1 ∈ edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
    (doubledBoxOriginToInnerEndpointSource n w)
    (doubledBoxInnerPairSource n v w) d.1
  exact edgeCopySourcePairData_mem_witnesses (FK.boxGraph 3 (2 * n)) d

set_option linter.style.longLine false in

theorem doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourceEquations
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
    let profile := Function.update m p.2.1 (m p.2.1 - 1)
    let witness :=
      copyDeletePreimageDecrementEraseFinset
        (FK.boxGraph 3 (2 * n)) m p.2 p.1
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
        witness =
      doubledBoxOriginToInnerEndpointSource n v ∧
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
                profile)) \
          witness) =
        (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
  exact
    (edgeCopySourcePairWitnesses_mem (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n)))
      (Function.update m p.2.1 (m p.2.1 - 1))
      (copyDeletePreimageDecrementEraseFinset
        (FK.boxGraph 3 (2 * n)) m p.2 p.1)).mp
      (doubledBox_selectedEdgeCopyPairsInCurrent_decrementWitness_mem
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp)

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourceEquations
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
    let profile := Function.update m p.2.1 (m p.2.1 - 1)
    let witness :=
      copyDeletePreimageDecrementEraseFinset
        (FK.boxGraph 3 (2 * n)) m p.2 p.1
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
        witness =
      doubledBoxOriginToInnerEndpointSource n w ∧
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
                profile)) \
          witness) =
        doubledBoxInnerPairSource n v w := by
  exact
    (edgeCopySourcePairWitnesses_mem (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w)
      (Function.update m p.2.1 (m p.2.1 - 1))
      (copyDeletePreimageDecrementEraseFinset
        (FK.boxGraph 3 (2 * n)) m p.2 p.1)).mp
      (doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementWitness_mem
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp)

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourceEquations
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
    let profile := Function.update m p.2.1 (m p.2.1 - 1)
    let witness :=
      copyDeletePreimageDecrementEraseFinset
        (FK.boxGraph 3 (2 * n)) m p.2 p.1
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
        witness =
      doubledBoxOriginToInnerEndpointSource n v ∧
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
                profile)) \
          witness) =
        (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
  exact
    (edgeCopySourcePairWitnesses_mem (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n)))
      (Function.update m p.2.1 (m p.2.1 - 1))
      (copyDeletePreimageDecrementEraseFinset
        (FK.boxGraph 3 (2 * n)) m p.2 p.1)).mp
      (doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementWitness_mem
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp)

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourceEquations
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
    let profile := Function.update m p.2.1 (m p.2.1 - 1)
    let witness :=
      copyDeletePreimageDecrementEraseFinset
        (FK.boxGraph 3 (2 * n)) m p.2 p.1
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
        witness =
      doubledBoxInnerPairSource n v w ∧
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
                profile)) \
          witness) =
        doubledBoxOriginToInnerEndpointSource n w := by
  exact
    (edgeCopySourcePairWitnesses_mem (FK.boxGraph 3 (2 * n))
      (doubledBoxInnerPairSource n v w)
      (doubledBoxOriginToInnerEndpointSource n w)
      (Function.update m p.2.1 (m p.2.1 - 1))
      (copyDeletePreimageDecrementEraseFinset
        (FK.boxGraph 3 (2 * n)) m p.2 p.1)).mp
      (doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementWitness_mem
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp)

end Exact3D
end StatMech
