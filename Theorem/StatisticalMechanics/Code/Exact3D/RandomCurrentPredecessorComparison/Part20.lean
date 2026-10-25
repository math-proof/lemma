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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part19
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementWitness_mem
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
    ((Finset.univ :
        Finset
          (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile)) \
      witness) ∈
      edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)
        profile := by
  let d :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairData
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
  change (edgeCopySourcePairData_swap (FK.boxGraph 3 (2 * n)) d).2.1 ∈
    edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w)
      (edgeCopySourcePairData_swap (FK.boxGraph 3 (2 * n)) d).1
  exact edgeCopySourcePairData_mem_witnesses (FK.boxGraph 3 (2 * n))
    (edgeCopySourcePairData_swap (FK.boxGraph 3 (2 * n)) d)

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementSourceEquations
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
      (Finset.univ :
          Finset
            (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile)) \
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
      ((Finset.univ :
          Finset
            (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
              (Function.update m p.2.1 (m p.2.1 - 1)))) \
        copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m p.2 p.1)).mp
      (doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementWitness_mem
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp)

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourceEquations
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
      (doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementWitness_mem
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp)

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_eq_of_selectedCopy_eq_of_decrementWitness_eq
    {n : ℕ} {w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    {p q : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0)
    (hq :
      q ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0)
    (hcopy : p.2 = q.2)
    (hmap :
      copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m p.2 p.1 =
        copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m p.2 q.1) :
    p = q := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n w)
      (m := m) (e0 := e0) p).mp hp
  have hqbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n w)
      (m := m) (e0 := e0) q).mp hq
  have hqmem : p.2 ∈ q.1 := by
    simpa [hcopy] using hqbranch.2
  have hK : p.1 = q.1 :=
    copyDeletePreimageDecrementEraseFinset_injective_of_mem
      (FK.boxGraph 3 (2 * n)) m p.2 hpbranch.2 hqmem hmap
  rcases p with ⟨K, i⟩
  rcases q with ⟨L, j⟩
  dsimp at hK hcopy
  subst L
  subst j
  rfl

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_eq_of_selectedCopy_eq_of_decrementWitness_eq
    {n : ℕ} {w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    {p q : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0)
    (hq :
      q ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0)
    (hcopy : p.2 = q.2)
    (hmap :
      copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m p.2 p.1 =
        copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m p.2 q.1) :
    p = q := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n w)
      (m := m) (e0 := e0) p).mp hp
  have hqbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n w)
      (m := m) (e0 := e0) q).mp hq
  have hqnot : p.2 ∉ q.1 := by
    simpa [hcopy] using hqbranch.2
  have hK : p.1 = q.1 :=
    copyDeletePreimageDecrementEraseFinset_injective_of_not_mem
      (FK.boxGraph 3 (2 * n)) m p.2 hpbranch.2 hqnot hmap
  rcases p with ⟨K, i⟩
  rcases q with ⟨L, j⟩
  dsimp at hK hcopy
  subst L
  subst j
  rfl

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_eq_of_selectedCopy_eq_of_decrementWitness_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    {p q : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
      Sharpness.FluxEdgeCopy.Copy G m)}
    (hp : p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0)
    (hq : q ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0)
    (hcopy : p.2 = q.2)
    (hmap :
      copyDeletePreimageDecrementEraseFinset G m p.2 p.1 =
        copyDeletePreimageDecrementEraseFinset G m p.2 q.1) :
    p = q := by
  classical
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      (G := G) (A := A) (m := m) (e0 := e0) p).mp hp
  have hqbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      (G := G) (A := A) (m := m) (e0 := e0) q).mp hq
  have hqnot : p.2 ∉ q.1 := by
    simpa [hcopy] using hqbranch.2
  have hK : p.1 = q.1 :=
    copyDeletePreimageDecrementEraseFinset_injective_of_not_mem
      G m p.2 hpbranch.2 hqnot hmap
  rcases p with ⟨K, i⟩
  rcases q with ⟨L, j⟩
  dsimp at hK hcopy
  subst L
  subst j
  rfl

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_eq_of_fixedCopy_swapped_decrementSourcePairData_eq
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)
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
    {p q : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxInnerPairSource n v w) m e0).filter
          (fun p => p.2 = i))
    (hq :
      q ∈
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxInnerPairSource n v w) m e0).filter
          (fun p => p.2 = i))
    (hroute :
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementSourcePairData
          (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw
          (p := p) (Finset.mem_filter.mp hp).1 =
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementSourcePairData
          (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw
          (p := q) (Finset.mem_filter.mp hq).1) :
    p = q := by
  classical
  rcases p with ⟨K, ip⟩
  rcases q with ⟨L, iq⟩
  let G := FK.boxGraph 3 (2 * n)
  have hpbranch :
      (⟨K, ip⟩ :
        Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m) =>
          Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)) ∈
        edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxInnerPairSource n v w) m e0 :=
    (Finset.mem_filter.mp hp).1
  have hqbranch :
      (⟨L, iq⟩ :
        Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m) =>
          Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)) ∈
        edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxInnerPairSource n v w) m e0 :=
    (Finset.mem_filter.mp hq).1
  have hpi : ip = i := (Finset.mem_filter.mp hp).2
  have hqi : iq = i := (Finset.mem_filter.mp hq).2
  subst i
  have hiq : iq = ip := hqi
  subst iq
  have hcopy :
      (⟨K, ip⟩ :
        Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m) =>
          Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)).2 =
        (⟨L, ip⟩ :
          Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m) =>
            Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)).2 := rfl
  let dp :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairData
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw
      (p := ⟨K, ip⟩) hpbranch
  let dq :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairData
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw
      (p := ⟨L, ip⟩) hqbranch
  have hdata : dp = dq := by
    exact
      (edgeCopySourcePairData_swap_injective
        (G := G)
        (A := doubledBoxInnerPairSource n v w)
        (B := doubledBoxOriginToInnerEndpointSource n w))
        (by
          simpa
            [G, dp, dq,
              doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementSourcePairData]
            using hroute)
  let profile := Function.update m ip.1 (m ip.1 - 1)
  have hW :
      edgeCopySourcePairDataWitnessAt
          (FK.boxGraph 3 (2 * n))
          (A := doubledBoxInnerPairSource n v w)
          (B := doubledBoxOriginToInnerEndpointSource n w)
          profile dp =
        edgeCopySourcePairDataWitnessAt
          (FK.boxGraph 3 (2 * n))
          (A := doubledBoxInnerPairSource n v w)
          (B := doubledBoxOriginToInnerEndpointSource n w)
          profile dq := by
    simpa [G] using
      congrArg
        (edgeCopySourcePairDataWitnessAt
          (FK.boxGraph 3 (2 * n))
          (A := doubledBoxInnerPairSource n v w)
          (B := doubledBoxOriginToInnerEndpointSource n w)
          profile) hdata
  have hdq_profile : dq.1 = profile := by
    rfl
  have hmap :
      copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m ip K =
        copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m ip L := by
    simpa
      [dp, dq, profile, hdq_profile, hcopy,
        edgeCopySourcePairDataWitnessAt,
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairData]
      using hW
  exact
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_eq_of_selectedCopy_eq_of_decrementWitness_eq
      (FK.boxGraph 3 (2 * n)) (doubledBoxInnerPairSource n v w) m e0
      hpbranch hqbranch hcopy hmap

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementSourcePairData_fixedCopy_injective
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)
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
    Function.Injective
      (fun p :
          {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m) =>
            Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m) //
            p ∈
              (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
                (FK.boxGraph 3 (2 * n))
                (doubledBoxInnerPairSource n v w) m e0).filter
                (fun p => p.2 = i)} =>
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementSourcePairData
          (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw
          (p := p.1) (Finset.mem_filter.mp p.2).1) := by
  intro p q hroute
  apply Subtype.ext
  exact
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_eq_of_fixedCopy_swapped_decrementSourcePairData_eq
      (n := n) (v := v) (w := w) m e0 i hedge hfull hov how hvw
      (p := p.1) (q := q.1) p.2 q.2 hroute

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_copyFiber_card_le_witnesses
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)
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
    ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0).filter
        (fun p => p.2 = i)).card ≤
      (edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n)))
        (Function.update m i.1 (m i.1 - 1))).card := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let S :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) m e0).filter
      (fun p => p.2 = i)
  let T :=
    edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n)))
      (Function.update m i.1 (m i.1 - 1))
  change S.card ≤ T.card
  refine
    Finset.card_le_card_of_injOn
      (fun p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
          (FK.boxGraph 3 (2 * n)) m) =>
        Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m) =>
        copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m i p.1) ?_ ?_
  · intro p hpS
    have hpbranch :
        p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0 :=
      (Finset.mem_filter.mp hpS).1
    have hpi : p.2 = i := (Finset.mem_filter.mp hpS).2
    have hw :=
      doubledBox_selectedEdgeCopyPairsInCurrent_decrementWitness_mem
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hpbranch
    subst i
    simpa [T] using hw
  · intro p hpS q hqS hmap
    have hpbranch :
        p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0 :=
      (Finset.mem_filter.mp hpS).1
    have hqbranch :
        q ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0 :=
      (Finset.mem_filter.mp hqS).1
    have hpi : p.2 = i := (Finset.mem_filter.mp hpS).2
    have hqi : q.2 = i := (Finset.mem_filter.mp hqS).2
    subst i
    have hcopy : p.2 = q.2 := hqi.symm
    have hmap' :
        copyDeletePreimageDecrementEraseFinset
            (FK.boxGraph 3 (2 * n)) m p.2 p.1 =
          copyDeletePreimageDecrementEraseFinset
            (FK.boxGraph 3 (2 * n)) m p.2 q.1 := by
      simpa using hmap
    exact
      doubledBox_selectedEdgeCopyPairsInCurrent_eq_of_selectedCopy_eq_of_decrementWitness_eq
        (n := n) (w := w) m e0 hpbranch hqbranch hcopy hmap'

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_copyFiber_card_le_witnesses
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)
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
    ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0).filter
        (fun p => p.2 = i)).card ≤
      (edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)
        (Function.update m i.1 (m i.1 - 1))).card := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let S :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) m e0).filter
      (fun p => p.2 = i)
  let T :=
    edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w)
      (Function.update m i.1 (m i.1 - 1))
  change S.card ≤ T.card
  refine
    Finset.card_le_card_of_injOn
      (fun p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
          (FK.boxGraph 3 (2 * n)) m) =>
        Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m) =>
        copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m i p.1) ?_ ?_
  · intro p hpS
    have hpbranch :
        p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0 :=
      (Finset.mem_filter.mp hpS).1
    have hpi : p.2 = i := (Finset.mem_filter.mp hpS).2
    have hw :=
      doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementWitness_mem
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hpbranch
    subst i
    simpa [T] using hw
  · intro p hpS q hqS hmap
    have hpbranch :
        p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0 :=
      (Finset.mem_filter.mp hpS).1
    have hqbranch :
        q ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0 :=
      (Finset.mem_filter.mp hqS).1
    have hpi : p.2 = i := (Finset.mem_filter.mp hpS).2
    have hqi : q.2 = i := (Finset.mem_filter.mp hqS).2
    subst i
    have hcopy : p.2 = q.2 := hqi.symm
    have hmap' :
        copyDeletePreimageDecrementEraseFinset
            (FK.boxGraph 3 (2 * n)) m p.2 p.1 =
          copyDeletePreimageDecrementEraseFinset
            (FK.boxGraph 3 (2 * n)) m p.2 q.1 := by
      simpa using hmap
    exact
      doubledBox_selectedEdgeCopyPairsOutsideCurrent_eq_of_selectedCopy_eq_of_decrementWitness_eq
        (n := n) (w := w) m e0 hpbranch hqbranch hcopy hmap'

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_copyFiber_card_le_witnesses
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)
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
    ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v w) m e0).filter
        (fun p => p.2 = i)).card ≤
      (edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v w)
        (doubledBoxOriginToInnerEndpointSource n w)
        (Function.update m i.1 (m i.1 - 1))).card := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let S :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxInnerPairSource n v w) m e0).filter
      (fun p => p.2 = i)
  let T :=
    edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
      (doubledBoxInnerPairSource n v w)
      (doubledBoxOriginToInnerEndpointSource n w)
      (Function.update m i.1 (m i.1 - 1))
  change S.card ≤ T.card
  refine
    Finset.card_le_card_of_injOn
      (fun p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
          (FK.boxGraph 3 (2 * n)) m) =>
        Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m) =>
        copyDeletePreimageDecrementEraseFinset
          (FK.boxGraph 3 (2 * n)) m i p.1) ?_ ?_
  · intro p hpS
    have hpbranch :
        p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxInnerPairSource n v w) m e0 :=
      (Finset.mem_filter.mp hpS).1
    have hpi : p.2 = i := (Finset.mem_filter.mp hpS).2
    have hw :=
      doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementWitness_mem
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hpbranch
    subst i
    simpa [T] using hw
  · intro p hpS q hqS hmap
    have hpbranch :
        p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxInnerPairSource n v w) m e0 :=
      (Finset.mem_filter.mp hpS).1
    have hqbranch :
        q ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxInnerPairSource n v w) m e0 :=
      (Finset.mem_filter.mp hqS).1
    have hpi : p.2 = i := (Finset.mem_filter.mp hpS).2
    have hqi : q.2 = i := (Finset.mem_filter.mp hqS).2
    subst i
    have hcopy : p.2 = q.2 := hqi.symm
    have hmap' :
        copyDeletePreimageDecrementEraseFinset
            (FK.boxGraph 3 (2 * n)) m p.2 p.1 =
          copyDeletePreimageDecrementEraseFinset
            (FK.boxGraph 3 (2 * n)) m p.2 q.1 := by
      simpa using hmap
    exact
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_eq_of_selectedCopy_eq_of_decrementWitness_eq
        (FK.boxGraph 3 (2 * n)) (doubledBoxInnerPairSource n v w)
        m e0 hpbranch hqbranch hcopy hmap'

set_option linter.style.longLine false in

theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_eq_sum_selectedCopy_image_fibers
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).card =
      ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).image
          (fun p => p.2),
        ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).filter
          (fun p => p.2 = i)).card := by
  classical
  simpa using
    Finset.card_eq_sum_card_image
      (fun p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
        Sharpness.FluxEdgeCopy.Copy G m) => p.2)
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0)

set_option linter.style.longLine false in

theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_card_eq_sum_selectedCopy_image_fibers
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).card =
      ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).image
          (fun p => p.2),
        ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).filter
          (fun p => p.2 = i)).card := by
  classical
  simpa using
    Finset.card_eq_sum_card_image
      (fun p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
        Sharpness.FluxEdgeCopy.Copy G m) => p.2)
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0)

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_selectedCopy_image_card_le_edgeMultiplicity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    ((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).image
        (fun p => p.2)).card ≤ m e0 := by
  classical
  have hsubset :
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).image
          (fun p => p.2) ⊆ edgeCopyCopiesOfEdge G m e0 := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨p, hp, hpi⟩
    have hpbranch :=
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem G A m e0 p).mp hp
    have hpedge :=
      (edgeCopySourceSectorSelectedEdgeCopyPairs_mem G A m e0 p).mp
        hpbranch.1
    exact
      (edgeCopyCopiesOfEdge_mem G m e0 i).mpr (by
        rw [← hpi]
        exact hpedge.2)
  have hcard :=
    Finset.card_le_card hsubset
  simpa [edgeCopyCopiesOfEdge_card] using hcard

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_selectedCopy_image_card_le_edgeMultiplicity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).image
        (fun p => p.2)).card ≤ m e0 := by
  classical
  have hsubset :
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).image
          (fun p => p.2) ⊆ edgeCopyCopiesOfEdge G m e0 := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨p, hp, hpi⟩
    have hpbranch :=
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem G A m e0 p).mp hp
    have hpedge :=
      (edgeCopySourceSectorSelectedEdgeCopyPairs_mem G A m e0 p).mp
        hpbranch.1
    exact
      (edgeCopyCopiesOfEdge_mem G m e0 i).mpr (by
        rw [← hpi]
        exact hpedge.2)
  have hcard :=
    Finset.card_le_card hsubset
  simpa [edgeCopyCopiesOfEdge_card] using hcard

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_selectedCopyImage_decrementSummand_sum_eq_card_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V)
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).image
        (fun p => p.2),
      edgeCopySourcePairSummand G β J B C
        (Function.update m i.1 (m i.1 - 1))) =
      (((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).image
        (fun p => p.2)).card : ℝ) *
        edgeCopySourcePairSummand G β J B C
          (Function.update m e0 (m e0 - 1)) := by
  classical
  let S := edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0
  let W :=
    edgeCopySourcePairSummand G β J B C
      (Function.update m e0 (m e0 - 1))
  have hconst :
      ∀ i ∈ S.image (fun p => p.2),
        edgeCopySourcePairSummand G β J B C
          (Function.update m i.1 (m i.1 - 1)) = W := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨p, hp, hpi⟩
    have hpbranch :=
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem G A m e0 p).mp
        (by simpa [S] using hp)
    have hpedge :=
      (edgeCopySourceSectorSelectedEdgeCopyPairs_mem G A m e0 p).mp
        hpbranch.1
    have hiedge : i.1 = e0 := by
      rw [← hpi]
      exact hpedge.2
    simp [W, hiedge]
  calc
    (∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).image
        (fun p => p.2),
      edgeCopySourcePairSummand G β J B C
        (Function.update m i.1 (m i.1 - 1)))
        = ∑ _i ∈ S.image (fun p => p.2), W := by
          refine Finset.sum_congr ?_ ?_
          · rfl
          · intro i hi
            exact hconst i hi
    _ = (((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).image
        (fun p => p.2)).card : ℝ) *
        edgeCopySourcePairSummand G β J B C
          (Function.update m e0 (m e0 - 1)) := by
      rw [Finset.sum_const, nsmul_eq_mul]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_selectedCopyImage_decrementSummand_sum_eq_card_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V)
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).image
        (fun p => p.2),
      edgeCopySourcePairSummand G β J B C
        (Function.update m i.1 (m i.1 - 1))) =
      (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).image
        (fun p => p.2)).card : ℝ) *
        edgeCopySourcePairSummand G β J B C
          (Function.update m e0 (m e0 - 1)) := by
  classical
  let S := edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0
  let W :=
    edgeCopySourcePairSummand G β J B C
      (Function.update m e0 (m e0 - 1))
  have hconst :
      ∀ i ∈ S.image (fun p => p.2),
        edgeCopySourcePairSummand G β J B C
          (Function.update m i.1 (m i.1 - 1)) = W := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨p, hp, hpi⟩
    have hpbranch :=
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem G A m e0 p).mp
        (by simpa [S] using hp)
    have hpedge :=
      (edgeCopySourceSectorSelectedEdgeCopyPairs_mem G A m e0 p).mp
        hpbranch.1
    have hiedge : i.1 = e0 := by
      rw [← hpi]
      exact hpedge.2
    simp [W, hiedge]
  calc
    (∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).image
        (fun p => p.2),
      edgeCopySourcePairSummand G β J B C
        (Function.update m i.1 (m i.1 - 1)))
        = ∑ _i ∈ S.image (fun p => p.2), W := by
          refine Finset.sum_congr ?_ ?_
          · rfl
          · intro i hi
            exact hconst i hi
    _ = (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).image
        (fun p => p.2)).card : ℝ) *
        edgeCopySourcePairSummand G β J B C
          (Function.update m e0 (m e0 - 1)) := by
      rw [Finset.sum_const, nsmul_eq_mul]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_selectedCopyImage_decrementSummand_sum_le_edgeMultiplicity_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V)
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) :
    (∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).image
        (fun p => p.2),
      edgeCopySourcePairSummand G β J B C
        (Function.update m i.1 (m i.1 - 1))) ≤
      (m e0 : ℝ) *
        edgeCopySourcePairSummand G β J B C
          (Function.update m e0 (m e0 - 1)) := by
  rw [edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_selectedCopyImage_decrementSummand_sum_eq_card_mul]
  have hcard_nat :=
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_selectedCopy_image_card_le_edgeMultiplicity
      G A m e0
  have hcard :
      (((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A m e0).image
        (fun p => p.2)).card : ℝ) ≤ (m e0 : ℝ) := by
    exact_mod_cast hcard_nat
  have hnonneg :
      0 ≤ edgeCopySourcePairSummand G β J B C
        (Function.update m e0 (m e0 - 1)) :=
    edgeCopySourcePairSummand_nonneg G β J B C
      (Function.update m e0 (m e0 - 1)) hβ hJ
  exact mul_le_mul_of_nonneg_right hcard hnonneg

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_selectedCopyImage_decrementSummand_sum_le_edgeMultiplicity_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V)
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) :
    (∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).image
        (fun p => p.2),
      edgeCopySourcePairSummand G β J B C
        (Function.update m i.1 (m i.1 - 1))) ≤
      (m e0 : ℝ) *
        edgeCopySourcePairSummand G β J B C
          (Function.update m e0 (m e0 - 1)) := by
  rw [edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_selectedCopyImage_decrementSummand_sum_eq_card_mul]
  have hcard_nat :=
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_selectedCopy_image_card_le_edgeMultiplicity
      G A m e0
  have hcard :
      (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A m e0).image
        (fun p => p.2)).card : ℝ) ≤ (m e0 : ℝ) := by
    exact_mod_cast hcard_nat
  have hnonneg :
      0 ≤ edgeCopySourcePairSummand G β J B C
        (Function.update m e0 (m e0 - 1)) :=
    edgeCopySourcePairSummand_nonneg G β J B C
      (Function.update m e0 (m e0 - 1)) hβ hJ
  exact mul_le_mul_of_nonneg_right hcard hnonneg

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_card_le_selectedCopyImage_witness_sum
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
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0).card ≤
      ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0).image
          (fun p => p.2),
        (edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n)))
          (Function.update m i.1 (m i.1 - 1))).card := by
  classical
  rw [edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_eq_sum_selectedCopy_image_fibers]
  refine Finset.sum_le_sum ?_
  intro i _hi
  exact
    doubledBox_selectedEdgeCopyPairsInCurrent_copyFiber_card_le_witnesses
      (n := n) (v := v) (w := w) m e0 i hedge hfull hov how hvw

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_card_le_selectedCopyImage_witness_sum
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
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0).card ≤
      ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0).image
          (fun p => p.2),
        (edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)
          (Function.update m i.1 (m i.1 - 1))).card := by
  classical
  rw [edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_card_eq_sum_selectedCopy_image_fibers]
  refine Finset.sum_le_sum ?_
  intro i _hi
  exact
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_copyFiber_card_le_witnesses
      (n := n) (v := v) (w := w) m e0 i hedge hfull hov how hvw

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_card_le_selectedCopyImage_witness_sum
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
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v w) m e0).card ≤
      ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxInnerPairSource n v w) m e0).image
          (fun p => p.2),
        (edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
          (doubledBoxInnerPairSource n v w)
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m i.1 (m i.1 - 1))).card := by
  classical
  rw [edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_card_eq_sum_selectedCopy_image_fibers]
  refine Finset.sum_le_sum ?_
  intro i _hi
  exact
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_copyFiber_card_le_witnesses
      (n := n) (v := v) (w := w) m e0 i hedge hfull hov how hvw


theorem doubledBox_selectedEdgeCopy_weight_decrement
    {β : ℝ} {n : ℕ}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m) :
    ((m i.1 : ℝ) *
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)) =
      β *
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m i.1 (m i.1 - 1))) := by
  have hmpos : 0 < m i.1 :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) i.2.2
  simpa using
    weight_ofEdgeFun_decrement (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      m i.1 hmpos


theorem doubledBox_selectedEdgeCopy_weight_le_decrement
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m) :
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m i.1 (m i.1 - 1))) := by
  let w :=
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)
  have hmpos : 0 < m i.1 :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) i.2.2
  have hone_le : (1 : ℝ) ≤ (m i.1 : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hmpos
  have hw_nonneg : 0 ≤ w := by
    dsimp [w]
    exact
      weight_ofEdgeFun_nonneg_of_nonneg
        (FK.boxGraph 3 (2 * n)) β (fun _ => 1) hβ
        (by intro e; norm_num) m
  have hmul_le : w ≤ (m i.1 : ℝ) * w := by
    calc
      w = (1 : ℝ) * w := by ring
      _ ≤ (m i.1 : ℝ) * w :=
        mul_le_mul_of_nonneg_right hone_le hw_nonneg
  have hdecrement :=
    doubledBox_selectedEdgeCopy_weight_decrement (β := β) (n := n) m i
  exact hmul_le.trans_eq hdecrement

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopy_weight_div_six_div_384_le_beta_div_six_decrement
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m) :
    (((1 : ℝ) / 6) *
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)) /
        384 ≤
      ((β / 6) *
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m i.1 (m i.1 - 1)))) /
        384 := by
  have hweight :=
    doubledBox_selectedEdgeCopy_weight_le_decrement
      (β := β) (n := n) hβ m i
  calc
    (((1 : ℝ) / 6) *
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)) /
        384 ≤
        (((1 : ℝ) / 6) *
          (β *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (Function.update m i.1 (m i.1 - 1))))) /
          384 := by
      exact
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hweight (by norm_num)) (by norm_num)
    _ =
      ((β / 6) *
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m i.1 (m i.1 - 1)))) /
        384 := by
      ring

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_copyFiber_weight_sum_le_beta_mul_sourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)
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
    (∑ _p ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0).filter
        (fun p => p.2 = i),
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)) ≤
      β *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n)))
          (Function.update m i.1 (m i.1 - 1)) := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let B := (∅ : Finset (FK.boxVerts 3 (2 * n)))
  let m' := Function.update m i.1 (m i.1 - 1)
  let S :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) m e0).filter
      (fun p => p.2 = i)
  let T := edgeCopySourcePairWitnesses G A B m'
  let Wold :=
    Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m)
  let Wdec :=
    Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m')
  have hsum_eq :
      (∑ _p ∈ S, Wold) = (S.card : ℝ) * Wold := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_nat : S.card ≤ T.card := by
    simpa [S, T, G, A, B, m'] using
      doubledBox_selectedEdgeCopyPairsInCurrent_copyFiber_card_le_witnesses
        (n := n) (v := v) (w := w) m e0 i hedge hfull hov how hvw
  have hcard : (S.card : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast hcard_nat
  have hWold_nonneg : 0 ≤ Wold := by
    dsimp [Wold, G]
    exact
      weight_ofEdgeFun_nonneg_of_nonneg
        (FK.boxGraph 3 (2 * n)) β (fun _ => 1) hβ
        (by intro e; norm_num) m
  have hWold_le : Wold ≤ β * Wdec := by
    dsimp [Wold, Wdec, G, m']
    exact doubledBox_selectedEdgeCopy_weight_le_decrement (n := n) hβ m i
  have hT_nonneg : 0 ≤ (T.card : ℝ) := by positivity
  calc
    (∑ _p ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0).filter
        (fun p => p.2 = i),
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))
        = (∑ _p ∈ S, Wold) := by
          rfl
    _ = (S.card : ℝ) * Wold := hsum_eq
    _ ≤ (T.card : ℝ) * Wold :=
      mul_le_mul_of_nonneg_right hcard hWold_nonneg
    _ ≤ (T.card : ℝ) * (β * Wdec) :=
      mul_le_mul_of_nonneg_left hWold_le hT_nonneg
    _ = β * ((T.card : ℝ) * Wdec) := by ring
    _ = β * edgeCopySourcePairSummand G β (fun _ => 1) A B m' := by
      rw [edgeCopySourcePairSummand_eq_witness_card_mul_weight]
    _ =
      β *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n)))
          (Function.update m i.1 (m i.1 - 1)) := by
      rfl

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_copyFiber_weight_sum_le_beta_mul_sourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)
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
    (∑ _p ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0).filter
        (fun p => p.2 = i),
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)) ≤
      β *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)
          (Function.update m i.1 (m i.1 - 1)) := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n w
  let B := doubledBoxInnerPairSource n v w
  let m' := Function.update m i.1 (m i.1 - 1)
  let S :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) m e0).filter
      (fun p => p.2 = i)
  let T := edgeCopySourcePairWitnesses G A B m'
  let Wold :=
    Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m)
  let Wdec :=
    Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m')
  have hsum_eq :
      (∑ _p ∈ S, Wold) = (S.card : ℝ) * Wold := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_nat : S.card ≤ T.card := by
    simpa [S, T, G, A, B, m'] using
      doubledBox_selectedEdgeCopyPairsOutsideCurrent_copyFiber_card_le_witnesses
        (n := n) (v := v) (w := w) m e0 i hedge hfull hov how hvw
  have hcard : (S.card : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast hcard_nat
  have hWold_nonneg : 0 ≤ Wold := by
    dsimp [Wold, G]
    exact
      weight_ofEdgeFun_nonneg_of_nonneg
        (FK.boxGraph 3 (2 * n)) β (fun _ => 1) hβ
        (by intro e; norm_num) m
  have hWold_le : Wold ≤ β * Wdec := by
    dsimp [Wold, Wdec, G, m']
    exact doubledBox_selectedEdgeCopy_weight_le_decrement (n := n) hβ m i
  have hT_nonneg : 0 ≤ (T.card : ℝ) := by positivity
  calc
    (∑ _p ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0).filter
        (fun p => p.2 = i),
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))
        = (∑ _p ∈ S, Wold) := by
          rfl
    _ = (S.card : ℝ) * Wold := hsum_eq
    _ ≤ (T.card : ℝ) * Wold :=
      mul_le_mul_of_nonneg_right hcard hWold_nonneg
    _ ≤ (T.card : ℝ) * (β * Wdec) :=
      mul_le_mul_of_nonneg_left hWold_le hT_nonneg
    _ = β * ((T.card : ℝ) * Wdec) := by ring
    _ = β * edgeCopySourcePairSummand G β (fun _ => 1) A B m' := by
      rw [edgeCopySourcePairSummand_eq_witness_card_mul_weight]
    _ =
      β *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)
          (Function.update m i.1 (m i.1 - 1)) := by
      rfl

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_copyFiber_weight_sum_le_beta_mul_sourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)
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
    (∑ _p ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v w) m e0).filter
        (fun p => p.2 = i),
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)) ≤
      β *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxInnerPairSource n v w)
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m i.1 (m i.1 - 1)) := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxInnerPairSource n v w
  let B := doubledBoxOriginToInnerEndpointSource n w
  let m' := Function.update m i.1 (m i.1 - 1)
  let S :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxInnerPairSource n v w) m e0).filter
      (fun p => p.2 = i)
  let T := edgeCopySourcePairWitnesses G A B m'
  let Wold :=
    Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m)
  let Wdec :=
    Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m')
  have hsum_eq :
      (∑ _p ∈ S, Wold) = (S.card : ℝ) * Wold := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_nat : S.card ≤ T.card := by
    simpa [S, T, G, A, B, m'] using
      doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_copyFiber_card_le_witnesses
        (n := n) (v := v) (w := w) m e0 i hedge hfull hov how hvw
  have hcard : (S.card : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast hcard_nat
  have hWold_nonneg : 0 ≤ Wold := by
    dsimp [Wold, G]
    exact
      weight_ofEdgeFun_nonneg_of_nonneg
        (FK.boxGraph 3 (2 * n)) β (fun _ => 1) hβ
        (by intro e; norm_num) m
  have hWold_le : Wold ≤ β * Wdec := by
    dsimp [Wold, Wdec, G, m']
    exact doubledBox_selectedEdgeCopy_weight_le_decrement (n := n) hβ m i
  have hT_nonneg : 0 ≤ (T.card : ℝ) := by positivity
  calc
    (∑ _p ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v w) m e0).filter
        (fun p => p.2 = i),
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))
        = (∑ _p ∈ S, Wold) := by
          rfl
    _ = (S.card : ℝ) * Wold := hsum_eq
    _ ≤ (T.card : ℝ) * Wold :=
      mul_le_mul_of_nonneg_right hcard hWold_nonneg
    _ ≤ (T.card : ℝ) * (β * Wdec) :=
      mul_le_mul_of_nonneg_left hWold_le hT_nonneg
    _ = β * ((T.card : ℝ) * Wdec) := by ring
    _ = β * edgeCopySourcePairSummand G β (fun _ => 1) A B m' := by
      rw [edgeCopySourcePairSummand_eq_witness_card_mul_weight]
    _ =
      β *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxInnerPairSource n v w)
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m i.1 (m i.1 - 1)) := by
      rfl

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_weight_sum_le_beta_mul_selectedCopyImage_sourcePairSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    (∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)) ≤
      β *
        ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m i.1 (m i.1 - 1)) := by
  classical
  let S :=
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) m e0
  let Wold :=
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)
  let F :
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m → ℝ :=
    fun i =>
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n)))
        (Function.update m i.1 (m i.1 - 1))
  have hpartition :
      (∑ _p ∈ S, Wold) =
        ∑ i ∈ S.image (fun p => p.2),
          ∑ _p ∈ S.filter (fun p => p.2 = i), Wold := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := S) (t := S.image (fun p => p.2)) (g := fun p => p.2)
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      (fun _p => Wold)]
  calc
    (∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))
        = (∑ _p ∈ S, Wold) := by
          rfl
    _ =
        ∑ i ∈ S.image (fun p => p.2),
          ∑ _p ∈ S.filter (fun p => p.2 = i), Wold :=
      hpartition
    _ ≤ ∑ i ∈ S.image (fun p => p.2), β * F i := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      exact
        doubledBox_selectedEdgeCopyPairsInCurrent_copyFiber_weight_sum_le_beta_mul_sourcePairSummand
          (n := n) (v := v) (w := w) hβ m e0 i hedge hfull hov how hvw
    _ = β * ∑ i ∈ S.image (fun p => p.2), F i := by
      rw [← Finset.mul_sum]
    _ =
      β *
        ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m i.1 (m i.1 - 1)) := by
      rfl

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_weight_sum_le_beta_mul_selectedCopyImage_sourcePairSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    (∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)) ≤
      β *
        ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m i.1 (m i.1 - 1)) := by
  classical
  let S :=
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) m e0
  let Wold :=
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)
  let F :
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m → ℝ :=
    fun i =>
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)
        (Function.update m i.1 (m i.1 - 1))
  have hpartition :
      (∑ _p ∈ S, Wold) =
        ∑ i ∈ S.image (fun p => p.2),
          ∑ _p ∈ S.filter (fun p => p.2 = i), Wold := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := S) (t := S.image (fun p => p.2)) (g := fun p => p.2)
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      (fun _p => Wold)]
  calc
    (∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))
        = (∑ _p ∈ S, Wold) := by
          rfl
    _ =
        ∑ i ∈ S.image (fun p => p.2),
          ∑ _p ∈ S.filter (fun p => p.2 = i), Wold :=
      hpartition
    _ ≤ ∑ i ∈ S.image (fun p => p.2), β * F i := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      exact
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_copyFiber_weight_sum_le_beta_mul_sourcePairSummand
          (n := n) (v := v) (w := w) hβ m e0 i hedge hfull hov how hvw
    _ = β * ∑ i ∈ S.image (fun p => p.2), F i := by
      rw [← Finset.mul_sum]
    _ =
      β *
        ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m i.1 (m i.1 - 1)) := by
      rfl

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_weight_sum_le_beta_mul_selectedCopyImage_sourcePairSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    (∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v w) m e0,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)) ≤
      β *
        ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxInnerPairSource n v w) m e0).image
            (fun p => p.2),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxInnerPairSource n v w)
            (doubledBoxOriginToInnerEndpointSource n w)
            (Function.update m i.1 (m i.1 - 1)) := by
  classical
  let S :=
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxInnerPairSource n v w) m e0
  let Wold :=
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)
  let F :
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m → ℝ :=
    fun i =>
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxInnerPairSource n v w)
        (doubledBoxOriginToInnerEndpointSource n w)
        (Function.update m i.1 (m i.1 - 1))
  have hpartition :
      (∑ _p ∈ S, Wold) =
        ∑ i ∈ S.image (fun p => p.2),
          ∑ _p ∈ S.filter (fun p => p.2 = i), Wold := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := S) (t := S.image (fun p => p.2)) (g := fun p => p.2)
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      (fun _p => Wold)]
  calc
    (∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v w) m e0,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))
        = (∑ _p ∈ S, Wold) := by
          rfl
    _ =
        ∑ i ∈ S.image (fun p => p.2),
          ∑ _p ∈ S.filter (fun p => p.2 = i), Wold :=
      hpartition
    _ ≤ ∑ i ∈ S.image (fun p => p.2), β * F i := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      exact
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_copyFiber_weight_sum_le_beta_mul_sourcePairSummand
          (n := n) (v := v) (w := w) hβ m e0 i hedge hfull hov how hvw
    _ = β * ∑ i ∈ S.image (fun p => p.2), F i := by
      rw [← Finset.mul_sum]
    _ =
      β *
        ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxInnerPairSource n v w) m e0).image
            (fun p => p.2),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxInnerPairSource n v w)
            (doubledBoxOriginToInnerEndpointSource n w)
            (Function.update m i.1 (m i.1 - 1)) := by
      rfl

set_option linter.style.longLine false in

theorem doubledBox_selectedEdgeCopyPairsInCurrent_indicator_weight_sum_le_beta_mul_selectedCopyImage_sourcePairSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (if
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w then
      ∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0,
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)
    else
      0) ≤
      β *
        ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m i.1 (m i.1 - 1)) := by
  classical
  by_cases hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w
  · rw [if_pos hfull]
    exact
      doubledBox_selectedEdgeCopyPairsInCurrent_weight_sum_le_beta_mul_selectedCopyImage_sourcePairSummand_sum
        (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw
  · rw [if_neg hfull]
    have hsum_nonneg :
        0 ≤
          ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n w) m e0).image
              (fun p => p.2),
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n)))
              (Function.update m i.1 (m i.1 - 1)) := by
      refine Finset.sum_nonneg ?_
      intro i _hi
      exact
        edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n)))
          (Function.update m i.1 (m i.1 - 1))
          hβ (by intro e; norm_num)
    simpa using mul_nonneg hβ hsum_nonneg

set_option linter.style.longLine false in

theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_indicator_weight_sum_le_beta_mul_selectedCopyImage_sourcePairSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (if
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w then
      ∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0,
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)
    else
      0) ≤
      β *
        ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m i.1 (m i.1 - 1)) := by
  classical
  by_cases hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w
  · rw [if_pos hfull]
    exact
      doubledBox_selectedEdgeCopyPairsOutsideCurrent_weight_sum_le_beta_mul_selectedCopyImage_sourcePairSummand_sum
        (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw
  · rw [if_neg hfull]
    have hsum_nonneg :
        0 ≤
          ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n w) m e0).image
              (fun p => p.2),
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)
              (Function.update m i.1 (m i.1 - 1)) := by
      refine Finset.sum_nonneg ?_
      intro i _hi
      exact
        edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)
          (Function.update m i.1 (m i.1 - 1))
          hβ (by intro e; norm_num)
    simpa using mul_nonneg hβ hsum_nonneg

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_weight_le_decrementSourcePairDataWeight
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData
            m e0 hedge hfull hov how hvw hp) := by
  change
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m p.2.1 (m p.2.1 - 1)))
  exact doubledBox_selectedEdgeCopy_weight_le_decrement
    (n := n) hβ m p.2

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_weight_le_decrementSourcePairDataWeight
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData
            m e0 hedge hfull hov how hvw hp) := by
  change
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m p.2.1 (m p.2.1 - 1)))
  exact doubledBox_selectedEdgeCopy_weight_le_decrement
    (n := n) hβ m p.2

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_weight_le_decrementSourcePairDataWeight
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData
            m e0 hedge hfull hov how hvw hp) := by
  change
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m p.2.1 (m p.2.1 - 1)))
  exact doubledBox_selectedEdgeCopy_weight_le_decrement
    (n := n) hβ m p.2

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_weight_le_decrementSourcePairDataWeight
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairData
            m e0 hedge hfull hov how hvw hp) := by
  change
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m p.2.1 (m p.2.1 - 1)))
  exact doubledBox_selectedEdgeCopy_weight_le_decrement
    (n := n) hβ m p.2

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_weight_le_decrementSourcePairDataWeight
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementSourcePairData
            m e0 hedge hfull hov how hvw hp) := by
  simpa
    [doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementSourcePairData]
    using
      doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_weight_le_decrementSourcePairDataWeight
        (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw hp

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsInCurrent_switched_weight_le_decrementSourcePairDataWeight
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData
            m e0 hedge hfull hov how hvw hp) := by
  change
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m p.2.1 (m p.2.1 - 1)))
  exact doubledBox_selectedEdgeCopy_weight_le_decrement
    (n := n) hβ m p.2

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_weight_le_beta_mul_sourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n)))
          (Function.update m p.2.1 (m p.2.1 - 1)) := by
  let G := FK.boxGraph 3 (2 * n)
  let D :=
    doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
  have hweight_to_data :=
    doubledBox_selectedEdgeCopyPairsInCurrent_weight_le_decrementSourcePairDataWeight
      (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw hp
  have hD_nonneg :
      0 ≤ edgeCopySourcePairDataWeight G β (fun _ => 1) D := by
    dsimp [D, edgeCopySourcePairDataWeight, G]
    exact
      weight_ofEdgeFun_nonneg_of_nonneg G β (fun _ => 1) hβ
        (by intro e; norm_num)
        (Function.update m p.2.1 (m p.2.1 - 1))
  have hleD :=
    edgeCopySourcePairDataWeight_le_summand
      G β (fun _ => 1) D hD_nonneg
  have hmul :
      β * edgeCopySourcePairDataWeight G β (fun _ => 1) D ≤
        β *
          edgeCopySourcePairSummand G β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
    have h := mul_le_mul_of_nonneg_left hleD hβ
    simpa [D, G] using h
  exact hweight_to_data.trans hmul

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_weight_le_beta_mul_sourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)
          (Function.update m p.2.1 (m p.2.1 - 1)) := by
  let G := FK.boxGraph 3 (2 * n)
  let D :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
  have hweight_to_data :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_weight_le_decrementSourcePairDataWeight
      (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw hp
  have hD_nonneg :
      0 ≤ edgeCopySourcePairDataWeight G β (fun _ => 1) D := by
    dsimp [D, edgeCopySourcePairDataWeight, G]
    exact
      weight_ofEdgeFun_nonneg_of_nonneg G β (fun _ => 1) hβ
        (by intro e; norm_num)
        (Function.update m p.2.1 (m p.2.1 - 1))
  have hleD :=
    edgeCopySourcePairDataWeight_le_summand
      G β (fun _ => 1) D hD_nonneg
  have hmul :
      β * edgeCopySourcePairDataWeight G β (fun _ => 1) D ≤
        β *
          edgeCopySourcePairSummand G β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
    have h := mul_le_mul_of_nonneg_left hleD hβ
    simpa [D, G] using h
  exact hweight_to_data.trans hmul

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_weight_le_beta_mul_sourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n)))
          (Function.update m p.2.1 (m p.2.1 - 1)) := by
  let G := FK.boxGraph 3 (2 * n)
  let D :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
  have hweight_to_data :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_weight_le_decrementSourcePairDataWeight
      (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw hp
  have hD_nonneg :
      0 ≤ edgeCopySourcePairDataWeight G β (fun _ => 1) D := by
    dsimp [D, edgeCopySourcePairDataWeight, G]
    exact
      weight_ofEdgeFun_nonneg_of_nonneg G β (fun _ => 1) hβ
        (by intro e; norm_num)
        (Function.update m p.2.1 (m p.2.1 - 1))
  have hleD :=
    edgeCopySourcePairDataWeight_le_summand
      G β (fun _ => 1) D hD_nonneg
  have hmul :
      β * edgeCopySourcePairDataWeight G β (fun _ => 1) D ≤
        β *
          edgeCopySourcePairSummand G β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
    have h := mul_le_mul_of_nonneg_left hleD hβ
    simpa [D, G] using h
  exact hweight_to_data.trans hmul

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_weight_le_beta_mul_sourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxInnerPairSource n v w)
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m p.2.1 (m p.2.1 - 1)) := by
  let G := FK.boxGraph 3 (2 * n)
  let D :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairData
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
  have hweight_to_data :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_weight_le_decrementSourcePairDataWeight
      (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw hp
  have hD_nonneg :
      0 ≤ edgeCopySourcePairDataWeight G β (fun _ => 1) D := by
    dsimp [D, edgeCopySourcePairDataWeight, G]
    exact
      weight_ofEdgeFun_nonneg_of_nonneg G β (fun _ => 1) hβ
        (by intro e; norm_num)
        (Function.update m p.2.1 (m p.2.1 - 1))
  have hleD :=
    edgeCopySourcePairDataWeight_le_summand
      G β (fun _ => 1) D hD_nonneg
  have hmul :
      β * edgeCopySourcePairDataWeight G β (fun _ => 1) D ≤
        β *
          edgeCopySourcePairSummand G β (fun _ => 1)
            (doubledBoxInnerPairSource n v w)
            (doubledBoxOriginToInnerEndpointSource n w)
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
    have h := mul_le_mul_of_nonneg_left hleD hβ
    simpa [D, G] using h
  exact hweight_to_data.trans hmul

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_weight_le_beta_mul_sourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)
          (Function.update m p.2.1 (m p.2.1 - 1)) := by
  let G := FK.boxGraph 3 (2 * n)
  let D :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementSourcePairData
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
  have hweight_to_data :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_weight_le_decrementSourcePairDataWeight
      (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw hp
  have hD_nonneg :
      0 ≤ edgeCopySourcePairDataWeight G β (fun _ => 1) D := by
    dsimp
      [D, edgeCopySourcePairDataWeight, G,
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementSourcePairData]
    exact
      weight_ofEdgeFun_nonneg_of_nonneg G β (fun _ => 1) hβ
        (by intro e; norm_num)
        (Function.update m p.2.1 (m p.2.1 - 1))
  have hleD :=
    edgeCopySourcePairDataWeight_le_summand
      G β (fun _ => 1) D hD_nonneg
  have hmul :
      β * edgeCopySourcePairDataWeight G β (fun _ => 1) D ≤
        β *
          edgeCopySourcePairSummand G β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
    have h := mul_le_mul_of_nonneg_left hleD hβ
    simpa
      [D, G,
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementSourcePairData]
      using h
  exact hweight_to_data.trans hmul

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsInCurrent_switched_weight_le_beta_mul_sourcePairSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
      β *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)
          (Function.update m p.2.1 (m p.2.1 - 1)) := by
  let G := FK.boxGraph 3 (2 * n)
  let D :=
    doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
  have hweight_to_data :=
    doubledBox_selectedEdgeCopyPairsInCurrent_switched_weight_le_decrementSourcePairDataWeight
      (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw hp
  have hD_nonneg :
      0 ≤ edgeCopySourcePairDataWeight G β (fun _ => 1) D := by
    dsimp [D, edgeCopySourcePairDataWeight, G]
    exact
      weight_ofEdgeFun_nonneg_of_nonneg G β (fun _ => 1) hβ
        (by intro e; norm_num)
        (Function.update m p.2.1 (m p.2.1 - 1))
  have hleD :=
    edgeCopySourcePairDataWeight_le_summand
      G β (fun _ => 1) D hD_nonneg
  have hmul :
      β * edgeCopySourcePairDataWeight G β (fun _ => 1) D ≤
        β *
          edgeCopySourcePairSummand G β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
    have h := mul_le_mul_of_nonneg_left hleD hβ
    simpa [D, G] using h
  exact hweight_to_data.trans hmul

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_weight_sum_le_beta_mul_sourcePairSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    (∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)) ≤
      β *
        ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
  classical
  calc
    (∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))
        ≤
      ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0,
        β *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
      refine Finset.sum_le_sum ?_
      intro p hp
      exact
        doubledBox_selectedEdgeCopyPairsInCurrent_weight_le_beta_mul_sourcePairSummand
          (n := n) (v := v) (w := w) hβ m e0 hedge hfull
          hov how hvw hp
    _ =
      β *
        ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
      rw [← Finset.mul_sum]

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_weight_sum_le_beta_mul_sourcePairSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    (∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)) ≤
      β *
        ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
  classical
  calc
    (∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))
        ≤
      ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0,
        β *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
      refine Finset.sum_le_sum ?_
      intro p hp
      exact
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_weight_le_beta_mul_sourcePairSummand
          (n := n) (v := v) (w := w) hβ m e0 hedge hfull
          hov how hvw hp
    _ =
      β *
        ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
      rw [← Finset.mul_sum]

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_weight_sum_le_beta_mul_sourcePairSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
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
    (∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v w) m e0,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)) ≤
      β *
        ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxInnerPairSource n v w) m e0,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxInnerPairSource n v w)
            (doubledBoxOriginToInnerEndpointSource n w)
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
  classical
  calc
    (∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v w) m e0,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))
        ≤
      ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxInnerPairSource n v w) m e0,
        β *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxInnerPairSource n v w)
            (doubledBoxOriginToInnerEndpointSource n w)
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
      refine Finset.sum_le_sum ?_
      intro p hp
      exact
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_weight_le_beta_mul_sourcePairSummand
          (n := n) (v := v) (w := w) hβ m e0 hedge hfull
          hov how hvw hp
    _ =
      β *
        ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxInnerPairSource n v w) m e0,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxInnerPairSource n v w)
            (doubledBoxOriginToInnerEndpointSource n w)
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
      rw [← Finset.mul_sum]

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_indicator_weight_sum_le_beta_mul_sourcePairSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (if
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w then
      ∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0,
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)
    else
      0) ≤
      β *
        ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
  classical
  by_cases hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w
  · rw [if_pos hfull]
    exact
      doubledBox_selectedEdgeCopyPairsInCurrent_weight_sum_le_beta_mul_sourcePairSummand_sum
        (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw
  · rw [if_neg hfull]
    have hsum_nonneg :
        0 ≤
          ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n w) m e0,
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n)))
              (Function.update m p.2.1 (m p.2.1 - 1)) := by
      refine Finset.sum_nonneg ?_
      intro p _hp
      exact
        edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n)))
          (Function.update m p.2.1 (m p.2.1 - 1))
          hβ (by intro e; norm_num)
    simpa using mul_nonneg hβ hsum_nonneg

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_indicator_weight_sum_le_beta_mul_sourcePairSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (if
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w then
      ∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0,
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)
    else
      0) ≤
      β *
        ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m p.2.1 (m p.2.1 - 1)) := by
  classical
  by_cases hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w
  · rw [if_pos hfull]
    exact
      doubledBox_selectedEdgeCopyPairsOutsideCurrent_weight_sum_le_beta_mul_sourcePairSummand_sum
        (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw
  · rw [if_neg hfull]
    have hsum_nonneg :
        0 ≤
          ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n w) m e0,
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)
              (Function.update m p.2.1 (m p.2.1 - 1)) := by
      refine Finset.sum_nonneg ?_
      intro p _hp
      exact
        edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)
          (Function.update m p.2.1 (m p.2.1 - 1))
          hβ (by intro e; norm_num)
    simpa using mul_nonneg hβ hsum_nonneg

set_option linter.style.longLine false in


theorem doubledBox_edge_count_mul_targetTerm_le_beta_mul_selectedEdgeCopyBranchSourcePairSummandSums
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    ((m e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m ≤
      β *
        ((∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m p.2.1 (m p.2.1 - 1))) +
          ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m p.2.1 (m p.2.1 - 1))) := by
  rw [doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm]
  rw [edgeCopySourceSectorSelectedEdgeCopyPairs_edge_count_mul_term_eq_inCurrent_add_outside
    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
    (doubledBoxOriginToInnerEndpointSource n w) m e0]
  have hin :=
    doubledBox_selectedEdgeCopyPairsInCurrent_indicator_weight_sum_le_beta_mul_sourcePairSummand_sum
      (n := n) (v := v) (w := w) hβ m e0 hedge hov how hvw
  have hout :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_indicator_weight_sum_le_beta_mul_sourcePairSummand_sum
      (n := n) (v := v) (w := w) hβ m e0 hedge hov how hvw
  calc
    (if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w then
        ∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0,
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)
      else
        0) +
      (if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w then
        ∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0,
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)
      else
        0)
        ≤
      β *
        ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m p.2.1 (m p.2.1 - 1)) +
        β *
          ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n w) m e0,
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)
              (Function.update m p.2.1 (m p.2.1 - 1)) :=
      add_le_add hin hout
    _ =
      β *
        ((∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m p.2.1 (m p.2.1 - 1))) +
          ∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m p.2.1 (m p.2.1 - 1))) := by
      ring

set_option linter.style.longLine false in


theorem doubledBox_edge_count_mul_targetTerm_le_beta_mul_selectedCopyImageBranchSourcePairSummandSums
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    ((m e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m ≤
      β *
        ((∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m i.1 (m i.1 - 1))) +
          ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m i.1 (m i.1 - 1))) := by
  rw [doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm]
  rw [edgeCopySourceSectorSelectedEdgeCopyPairs_edge_count_mul_term_eq_inCurrent_add_outside
    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
    (doubledBoxOriginToInnerEndpointSource n w) m e0]
  have hin :=
    doubledBox_selectedEdgeCopyPairsInCurrent_indicator_weight_sum_le_beta_mul_selectedCopyImage_sourcePairSummand_sum
      (n := n) (v := v) (w := w) hβ m e0 hedge hov how hvw
  have hout :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_indicator_weight_sum_le_beta_mul_selectedCopyImage_sourcePairSummand_sum
      (n := n) (v := v) (w := w) hβ m e0 hedge hov how hvw
  calc
    (if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w then
        ∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0,
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)
      else
        0) +
      (if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w then
        ∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0,
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)
      else
        0)
        ≤
      β *
        ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m i.1 (m i.1 - 1)) +
        β *
          ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2),
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)
              (Function.update m i.1 (m i.1 - 1)) :=
      add_le_add hin hout
    _ =
      β *
        ((∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m i.1 (m i.1 - 1))) +
          ∑ i ∈ (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m i.1 (m i.1 - 1))) := by
      ring

set_option linter.style.longLine false in


theorem doubledBox_edge_count_mul_targetTerm_le_beta_mul_selectedCopyImageCardFixedDecrementBranchSourcePairSummands
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    ((m e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m ≤
      β *
        ((((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2)).card : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m e0 (m e0 - 1)) +
          (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2)).card : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m e0 (m e0 - 1))) := by
  have h :=
    doubledBox_edge_count_mul_targetTerm_le_beta_mul_selectedCopyImageBranchSourcePairSummandSums
      (n := n) (v := v) (w := w) hβ m e0 hedge hov how hvw
  rw [edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_selectedCopyImage_decrementSummand_sum_eq_card_mul
      (G := FK.boxGraph 3 (2 * n)) (β := β) (J := fun _ => 1)
      (A := doubledBoxOriginToInnerEndpointSource n w)
      (B := doubledBoxOriginToInnerEndpointSource n v)
      (C := (∅ : Finset (FK.boxVerts 3 (2 * n)))) (m := m) (e0 := e0),
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_selectedCopyImage_decrementSummand_sum_eq_card_mul
      (G := FK.boxGraph 3 (2 * n)) (β := β) (J := fun _ => 1)
      (A := doubledBoxOriginToInnerEndpointSource n w)
      (B := doubledBoxOriginToInnerEndpointSource n w)
      (C := doubledBoxInnerPairSource n v w) (m := m) (e0 := e0)] at h
  exact h

set_option linter.style.longLine false in


theorem doubledBox_edge_count_mul_targetTerm_le_beta_mul_edgeMultiplicityFixedDecrementBranchSourcePairSummands
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    ((m e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m ≤
      β *
        (((m e0 : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update m e0 (m e0 - 1)) +
          ((m e0 : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (Function.update m e0 (m e0 - 1))) := by
  have h :=
    doubledBox_edge_count_mul_targetTerm_le_beta_mul_selectedCopyImageCardFixedDecrementBranchSourcePairSummands
      (n := n) (v := v) (w := w) hβ m e0 hedge hov how hvw
  have hin :
      (((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0).image
          (fun p => p.2)).card : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n)))
          (Function.update m e0 (m e0 - 1)) ≤
      ((m e0 : ℕ) : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n)))
          (Function.update m e0 (m e0 - 1)) := by
    have hcard_nat :=
      edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_selectedCopy_image_card_le_edgeMultiplicity
        (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n w)
        m e0
    have hcard :
        (((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2)).card : ℝ) ≤ ((m e0 : ℕ) : ℝ) := by
      exact_mod_cast hcard_nat
    have hnonneg :
        0 ≤ edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n)))
          (Function.update m e0 (m e0 - 1)) :=
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n)))
        (Function.update m e0 (m e0 - 1)) hβ (by intro e; norm_num)
    exact mul_le_mul_of_nonneg_right hcard hnonneg
  have hout :
      (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m e0).image
          (fun p => p.2)).card : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)
          (Function.update m e0 (m e0 - 1)) ≤
      ((m e0 : ℕ) : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)
          (Function.update m e0 (m e0 - 1)) := by
    have hcard_nat :=
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_selectedCopy_image_card_le_edgeMultiplicity
        (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n w)
        m e0
    have hcard :
        (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m e0).image
            (fun p => p.2)).card : ℝ) ≤ ((m e0 : ℕ) : ℝ) := by
      exact_mod_cast hcard_nat
    have hnonneg :
        0 ≤ edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)
          (Function.update m e0 (m e0 - 1)) :=
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)
        (Function.update m e0 (m e0 - 1)) hβ (by intro e; norm_num)
    exact mul_le_mul_of_nonneg_right hcard hnonneg
  have hsum := add_le_add hin hout
  exact h.trans (mul_le_mul_of_nonneg_left hsum hβ)

end Exact3D
end StatMech
