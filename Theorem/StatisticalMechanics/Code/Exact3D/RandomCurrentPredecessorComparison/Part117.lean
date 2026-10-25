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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part109
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_subset_finset_sourceEquation
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {rows : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hcell_subset :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      ∀ m : Profile,
        m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
          m ∈ rows)
    {EmptySplit : Type}
    (emptySplitRows :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows} →
        Finset EmptySplit)
    (emptyProfileRouteRows :
      (m : {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows}) →
        EmptySplit → ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (emptyWitnessRows :
      (m : {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows}) →
        (i : EmptySplit) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (emptyProfileRouteRows m i)))
    (hemptyLeft :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (emptyProfileRouteRows m i))
          (emptyWitnessRows m i) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hemptyRight :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (emptyProfileRouteRows m i))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (emptyProfileRouteRows m i))) \
            emptyWitnessRows m i) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hemptyInj :
      Set.InjOn
        (fun p :
            Sigma
              (fun _ :
                {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                  m ∈ rows} =>
                EmptySplit) =>
          emptyProfileRouteRows p.1 p.2)
        (rows.attach.sigma emptySplitRows))
    (hemptyPoint :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
            ∑ i ∈ emptySplitRows ⟨m, hm⟩,
              ((β / 6) *
                Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (Sharpness.ofEdgeFun
                    (FK.boxGraph 3 (2 * n))
                    (emptyProfileRouteRows ⟨m, hm⟩ i))) /
                384)
    {InnerSplit : Type}
    (innerSplitRows :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows} →
        Finset InnerSplit)
    (innerProfileRouteRows :
      (m : {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows}) →
        InnerSplit → ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (innerWitnessRows :
      (m : {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows}) →
        (i : InnerSplit) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) (innerProfileRouteRows m i)))
    (hinnerLeft :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (innerProfileRouteRows m i))
          (innerWitnessRows m i) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hinnerRight :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (innerProfileRouteRows m i))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (innerProfileRouteRows m i))) \
            innerWitnessRows m i) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hinnerInj :
      Set.InjOn
        (fun p :
            Sigma
              (fun _ :
                {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ //
                  m ∈ rows} =>
                InnerSplit) =>
          innerProfileRouteRows p.1 p.2)
        (rows.attach.sigma innerSplitRows))
    (hinnerPoint :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
            ∑ i ∈ innerSplitRows ⟨m, hm⟩,
              ((β / 6) *
                Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (Sharpness.ofEdgeFun
                    (FK.boxGraph 3 (2 * n))
                    (innerProfileRouteRows ⟨m, hm⟩ i))) /
                384) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt]
  refine ⟨rows, ?_, ?_, ?_⟩
  · simpa using hcell_subset
  · exact
      ⟨EmptySplit, emptySplitRows, emptyProfileRouteRows, emptyWitnessRows,
        hemptyLeft, hemptyRight, hemptyInj, hemptyPoint⟩
  · exact
      ⟨InnerSplit, innerSplitRows, innerProfileRouteRows, innerWitnessRows,
        hinnerLeft, hinnerRight, hinnerInj, hinnerPoint⟩

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_empty
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell_empty :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = ∅) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = ∅ := by
    simpa [cell, Ωactive, w] using hcell_empty
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt]
  refine ⟨(∅ : Finset Profile), ?_, ?_, ?_⟩
  · intro m hm
    have hmcell : m ∈ cell := by
      simpa [cell, Ωactive, w] using hm
    simp [hcell] at hmcell
  · refine
      ⟨Empty, (fun _ => (∅ : Finset Empty)),
        (fun _ i => Empty.elim i), (fun _ i => Empty.elim i), ?_, ?_,
        ?_, ?_⟩
    · intro _m i
      cases i
    · intro _m i
      cases i
    · intro p _hp _q _hq _hroute
      rcases p with ⟨_m, i⟩
      cases i
    · intro _m hm
      cases hm
  · refine
      ⟨Empty, (fun _ => (∅ : Finset Empty)),
        (fun _ i => Empty.elim i), (fun _ i => Empty.elim i), ?_, ?_,
        ?_, ?_⟩
    · intro _m i
      cases i
    · intro _m i
      cases i
    · intro p _hp _q _hq _hroute
      rcases p with ⟨_m, i⟩
      cases i
    · intro _m hm
      cases hm

set_option maxHeartbeats 500000 in


open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_subset_finset_emptySplits_nonpos
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {rows : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    (hcell_subset :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      ∀ m : Profile,
        m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
          m ∈ rows)
    (hemptyNonpos :
      ∀ m,
        ∀ _hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤ 0)
    (hinnerNonpos :
      ∀ m,
        ∀ _hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤ 0) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt]
  refine ⟨rows, ?_, ?_, ?_⟩
  · simpa using hcell_subset
  · refine
      ⟨Empty, (fun _ => (∅ : Finset Empty)),
        (fun _ i => Empty.elim i), (fun _ i => Empty.elim i), ?_, ?_,
        ?_, ?_⟩
    · intro _m i
      cases i
    · intro _m i
      cases i
    · intro p _hp _q _hq _hroute
      rcases p with ⟨_m, i⟩
      cases i
    · intro m hm
      simpa using hemptyNonpos m hm
  · refine
      ⟨Empty, (fun _ => (∅ : Finset Empty)),
        (fun _ i => Empty.elim i), (fun _ i => Empty.elim i), ?_, ?_,
        ?_, ?_⟩
    · intro _m i
      cases i
    · intro _m i
      cases i
    · intro p _hp _q _hq _hroute
      rcases p with ⟨_m, i⟩
      cases i
    · intro m hm
      simpa using hinnerNonpos m hm

set_option maxHeartbeats 500000 in


open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_subset_pair_emptySplits_nonpos
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 m1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hcell_subset :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      ∀ m : Profile,
        m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
          m ∈ ({m0, m1} : Finset Profile))
    (hemptyNonpos0 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤ 0)
    (hemptyNonpos1 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤ 0)
    (hinnerNonpos0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤ 0)
    (hinnerNonpos1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤ 0) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let Profile := ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ
  refine
    exactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_subset_finset_emptySplits_nonpos
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (rows := ({m0, m1} : Finset Profile)) ?_ ?_ ?_
  · simpa [Profile] using hcell_subset
  · intro m hm
    by_cases hm0 : m = m0
    · subst m
      simpa using hemptyNonpos0
    · have hm_or : m = m0 ∨ m = m1 := by
        simpa [Profile, Finset.mem_insert, Finset.mem_singleton] using hm
      have hm1 : m = m1 := hm_or.resolve_left hm0
      subst m
      simpa using hemptyNonpos1
  · intro m hm
    by_cases hm0 : m = m0
    · subst m
      simpa using hinnerNonpos0
    · have hm_or : m = m0 ∨ m = m1 := by
        simpa [Profile, Finset.mem_insert, Finset.mem_singleton] using hm
      have hm1 : m = m1 := hm_or.resolve_left hm0
      subst m
      simpa using hinnerNonpos1

set_option maxHeartbeats 700000 in


open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_subset_singleton_pointwise
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hcell_subset :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      ∀ m : Profile,
        m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
          m ∈ ({m0} : Finset Profile))
    {EmptySplit : Type}
    (emptySplit0 : Finset EmptySplit)
    (emptyProfileRoute0 :
      EmptySplit → ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (emptyWitness0 :
      (i : EmptySplit) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (emptyProfileRoute0 i)))
    (hemptyLeft0 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (emptyProfileRoute0 i))
          (emptyWitness0 i) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hemptyRight0 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (emptyProfileRoute0 i))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (emptyProfileRoute0 i))) \
            emptyWitness0 i) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hemptyInj0 : Set.InjOn emptyProfileRoute0 emptySplit0)
    (hemptyPoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ∑ i ∈ emptySplit0,
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun
                (FK.boxGraph 3 (2 * n)) (emptyProfileRoute0 i))) /
            384)
    {InnerSplit : Type}
    (innerSplit0 : Finset InnerSplit)
    (innerProfileRoute0 :
      InnerSplit → ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (innerWitness0 :
      (i : InnerSplit) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (innerProfileRoute0 i)))
    (hinnerLeft0 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (innerProfileRoute0 i))
          (innerWitness0 i) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hinnerRight0 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (innerProfileRoute0 i))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (innerProfileRoute0 i))) \
            innerWitness0 i) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hinnerInj0 : Set.InjOn innerProfileRoute0 innerSplit0)
    (hinnerPoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ∑ i ∈ innerSplit0,
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun
                (FK.boxGraph 3 (2 * n)) (innerProfileRoute0 i))) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Profile := ↥G.edgeFinset → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let rows : Finset Profile := {m0}
  let emptySplitRows : {m : Profile // m ∈ rows} → Finset EmptySplit :=
    fun _ => emptySplit0
  let emptyProfileRouteRows :
      (m : {m : Profile // m ∈ rows}) → EmptySplit → Profile :=
    fun _ i => emptyProfileRoute0 i
  let emptyWitnessRows :
      (m : {m : Profile // m ∈ rows}) → (i : EmptySplit) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (emptyProfileRouteRows m i)) :=
    fun _ i => emptyWitness0 i
  have hemptyInjRows :
      Set.InjOn
        (fun p : Sigma (fun _ : {m : Profile // m ∈ rows} => EmptySplit) =>
          emptyProfileRouteRows p.1 p.2)
        (rows.attach.sigma emptySplitRows) := by
    simpa [rows, emptySplitRows, emptyProfileRouteRows, G] using
      finset_singleton_attach_sigma_const_route_injOn
        (m0 := m0) emptySplit0 emptyProfileRoute0 hemptyInj0
  have hemptyPointRows :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
              β n v w e0 m ≤
            ∑ i ∈ emptySplitRows ⟨m, hm⟩,
              ((β / 6) *
                Sharpness.weight G β (fun _ => 1)
                  (Sharpness.ofEdgeFun G (emptyProfileRouteRows ⟨m, hm⟩ i))) /
                384 := by
    intro m hm
    have hm0 : m = m0 := by
      simpa [rows] using hm
    subst m
    simpa [rows, emptySplitRows, emptyProfileRouteRows, G, w] using hemptyPoint0
  let innerSplitRows : {m : Profile // m ∈ rows} → Finset InnerSplit :=
    fun _ => innerSplit0
  let innerProfileRouteRows :
      (m : {m : Profile // m ∈ rows}) → InnerSplit → Profile :=
    fun _ i => innerProfileRoute0 i
  let innerWitnessRows :
      (m : {m : Profile // m ∈ rows}) → (i : InnerSplit) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (innerProfileRouteRows m i)) :=
    fun _ i => innerWitness0 i
  have hinnerInjRows :
      Set.InjOn
        (fun p : Sigma (fun _ : {m : Profile // m ∈ rows} => InnerSplit) =>
          innerProfileRouteRows p.1 p.2)
        (rows.attach.sigma innerSplitRows) := by
    simpa [rows, innerSplitRows, innerProfileRouteRows, G] using
      finset_singleton_attach_sigma_const_route_injOn
        (m0 := m0) innerSplit0 innerProfileRoute0 hinnerInj0
  have hinnerPointRows :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v w e0 m ≤
            ∑ i ∈ innerSplitRows ⟨m, hm⟩,
              ((β / 6) *
                Sharpness.weight G β (fun _ => 1)
                  (Sharpness.ofEdgeFun G (innerProfileRouteRows ⟨m, hm⟩ i))) /
                384 := by
    intro m hm
    have hm0 : m = m0 := by
      simpa [rows] using hm
    subst m
    simpa [rows, innerSplitRows, innerProfileRouteRows, G, w] using hinnerPoint0
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt]
  refine ⟨rows, ?_, ?_, ?_⟩
  · simpa [rows, G, w] using hcell_subset
  · refine
      ⟨EmptySplit, emptySplitRows, emptyProfileRouteRows, emptyWitnessRows,
        ?_, ?_, hemptyInjRows, hemptyPointRows⟩
    · intro _m i
      simpa [emptyProfileRouteRows, emptyWitnessRows, G] using hemptyLeft0 i
    · intro _m i
      simpa [emptyProfileRouteRows, emptyWitnessRows, G] using hemptyRight0 i
  · refine
      ⟨InnerSplit, innerSplitRows, innerProfileRouteRows, innerWitnessRows,
        ?_, ?_, hinnerInjRows, hinnerPointRows⟩
    · intro _m i
      simpa [innerProfileRouteRows, innerWitnessRows, G, w] using hinnerLeft0 i
    · intro _m i
      simpa [innerProfileRouteRows, innerWitnessRows, G, w] using hinnerRight0 i

set_option maxHeartbeats 900000 in


open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt_of_emptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hsource :
      ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt]
    at hsource
  rcases hsource with
    ⟨rows, hcell_subset, hemptyData, hinnerData⟩
  rcases hemptyData with
    ⟨EmptySplit, emptySplitRows, emptyProfileRouteRows, emptyWitnessRows,
      hemptyLeft, hemptyRight, hemptyInj, hemptyPoint⟩
  rcases hinnerData with
    ⟨InnerSplit, innerSplitRows, innerProfileRouteRows, innerWitnessRows,
      hinnerLeft, hinnerRight, hinnerInj, hinnerPoint⟩
  exact
    exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt_of_cell_subset_finset_sourceEquation
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (rows := rows) hcell_subset
      emptySplitRows emptyProfileRouteRows emptyWitnessRows
      hemptyLeft hemptyRight hemptyInj hemptyPoint
      innerSplitRows innerProfileRouteRows innerWitnessRows
      hinnerLeft hinnerRight hinnerInj hinnerPoint

set_option maxHeartbeats 1000000 in


open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt_of_cell_subset_pair_pointwise
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 m1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hcell_subset :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      ∀ m : Profile,
        m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
          m ∈ ({m0, m1} : Finset Profile))
    {EmptySplit : Type}
    (emptySplit0 emptySplit1 : Finset EmptySplit)
    (emptyRoute0 emptyRoute1 :
      EmptySplit →
        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hemptyInj0 : Set.InjOn emptyRoute0 emptySplit0)
    (hemptyInj1 : Set.InjOn emptyRoute1 emptySplit1)
    (hemptyDisj :
      ∀ i ∈ emptySplit0, ∀ j ∈ emptySplit1,
        emptyRoute0 i ≠ emptyRoute1 j)
    (hemptyPoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ∑ i ∈ emptySplit0,
          ((β / 6) *
            edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (emptyRoute0 i)) /
            384)
    (hemptyPoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ∑ i ∈ emptySplit1,
          ((β / 6) *
            edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (emptyRoute1 i)) /
            384)
    {InnerSplit : Type}
    (innerSplit0 innerSplit1 : Finset InnerSplit)
    (innerRoute0 innerRoute1 :
      InnerSplit →
        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hinnerInj0 : Set.InjOn innerRoute0 innerSplit0)
    (hinnerInj1 : Set.InjOn innerRoute1 innerSplit1)
    (hinnerDisj :
      ∀ i ∈ innerSplit0, ∀ j ∈ innerSplit1,
        innerRoute0 i ≠ innerRoute1 j)
    (hinnerPoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ∑ i ∈ innerSplit0,
          ((β / 6) *
            edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (innerRoute0 i)) /
            384)
    (hinnerPoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ∑ i ∈ innerSplit1,
          ((β / 6) *
            edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (innerRoute1 i)) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Profile := ↥G.edgeFinset → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let rows : Finset Profile := {m0, m1}
  let emptySplitRows : {m : Profile // m ∈ rows} → Finset EmptySplit :=
    fun m => if m.1 = m0 then emptySplit0 else emptySplit1
  let emptyRouteRows :
      (m : {m : Profile // m ∈ rows}) → EmptySplit →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    fun m i => if m.1 = m0 then emptyRoute0 i else emptyRoute1 i
  have hemptyInjRows :
      Set.InjOn
        (fun p : Sigma (fun _ : {m : Profile // m ∈ rows} => EmptySplit) =>
          emptyRouteRows p.1 p.2)
        (rows.attach.sigma emptySplitRows) := by
    simpa [rows, emptySplitRows, emptyRouteRows, G] using
      finset_pair_attach_sigma_if_route_injOn
        (m0 := m0) (m1 := m1)
        emptySplit0 emptySplit1 emptyRoute0 emptyRoute1
        hemptyInj0 hemptyInj1 hemptyDisj
  have hemptyPointRows :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
              β n v w e0 m ≤
            ∑ i ∈ emptySplitRows ⟨m, hm⟩,
              ((β / 6) *
                edgeCopySourcePairDataWeight G β (fun _ => 1)
                  (emptyRouteRows ⟨m, hm⟩ i)) /
                384 := by
    intro m hm
    by_cases hm0 : m = m0
    · subst m
      simpa [emptySplitRows, emptyRouteRows, G, w] using hemptyPoint0
    · have hm_pair : m ∈ ({m0, m1} : Finset Profile) := by
        simpa [rows] using hm
      have hm_or : m = m0 ∨ m = m1 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hm_pair
      have hm1 : m = m1 := hm_or.resolve_left hm0
      subst m
      simpa [emptySplitRows, emptyRouteRows, G, w, hm0] using hemptyPoint1
  let innerSplitRows : {m : Profile // m ∈ rows} → Finset InnerSplit :=
    fun m => if m.1 = m0 then innerSplit0 else innerSplit1
  let innerRouteRows :
      (m : {m : Profile // m ∈ rows}) → InnerSplit →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) :=
    fun m i => if m.1 = m0 then innerRoute0 i else innerRoute1 i
  have hinnerInjRows :
      Set.InjOn
        (fun p : Sigma (fun _ : {m : Profile // m ∈ rows} => InnerSplit) =>
          innerRouteRows p.1 p.2)
        (rows.attach.sigma innerSplitRows) := by
    simpa [rows, innerSplitRows, innerRouteRows, G, w] using
      finset_pair_attach_sigma_if_route_injOn
        (m0 := m0) (m1 := m1)
        innerSplit0 innerSplit1 innerRoute0 innerRoute1
        hinnerInj0 hinnerInj1 hinnerDisj
  have hinnerPointRows :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v w e0 m ≤
            ∑ i ∈ innerSplitRows ⟨m, hm⟩,
              ((β / 6) *
                edgeCopySourcePairDataWeight G β (fun _ => 1)
                  (innerRouteRows ⟨m, hm⟩ i)) /
                384 := by
    intro m hm
    by_cases hm0 : m = m0
    · subst m
      simpa [innerSplitRows, innerRouteRows, G, w] using hinnerPoint0
    · have hm_pair : m ∈ ({m0, m1} : Finset Profile) := by
        simpa [rows] using hm
      have hm_or : m = m0 ∨ m = m1 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hm_pair
      have hm1 : m = m1 := hm_or.resolve_left hm0
      subst m
      simpa [innerSplitRows, innerRouteRows, G, w, hm0] using hinnerPoint1
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt]
  refine ⟨rows, ?_, ?_, ?_⟩
  · simpa [rows, G, w] using hcell_subset
  · exact
      ⟨EmptySplit, emptySplitRows, emptyRouteRows, hemptyInjRows,
        hemptyPointRows⟩
  · exact
      ⟨InnerSplit, innerSplitRows, innerRouteRows, hinnerInjRows,
        hinnerPointRows⟩

set_option maxHeartbeats 1000000 in


open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt_of_cell_subset_pair_sourceEquation_pointwise
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 m1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hcell_subset :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      ∀ m : Profile,
        m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
          m ∈ ({m0, m1} : Finset Profile))
    {EmptySplit : Type}
    (emptySplit0 emptySplit1 : Finset EmptySplit)
    (emptyProfileRoute0 emptyProfileRoute1 :
      EmptySplit → ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (emptyWitness0 :
      (i : EmptySplit) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (emptyProfileRoute0 i)))
    (emptyWitness1 :
      (i : EmptySplit) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (emptyProfileRoute1 i)))
    (hemptyLeft0 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (emptyProfileRoute0 i))
          (emptyWitness0 i) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hemptyRight0 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (emptyProfileRoute0 i))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (emptyProfileRoute0 i))) \
            emptyWitness0 i) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hemptyLeft1 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (emptyProfileRoute1 i))
          (emptyWitness1 i) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hemptyRight1 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (emptyProfileRoute1 i))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (emptyProfileRoute1 i))) \
            emptyWitness1 i) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hemptyInj0 : Set.InjOn emptyProfileRoute0 emptySplit0)
    (hemptyInj1 : Set.InjOn emptyProfileRoute1 emptySplit1)
    (hemptyDisj :
      ∀ i ∈ emptySplit0, ∀ j ∈ emptySplit1,
        emptyProfileRoute0 i ≠ emptyProfileRoute1 j)
    (hemptyPoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ∑ i ∈ emptySplit0,
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun
                (FK.boxGraph 3 (2 * n)) (emptyProfileRoute0 i))) /
            384)
    (hemptyPoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ∑ i ∈ emptySplit1,
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun
                (FK.boxGraph 3 (2 * n)) (emptyProfileRoute1 i))) /
            384)
    {InnerSplit : Type}
    (innerSplit0 innerSplit1 : Finset InnerSplit)
    (innerProfileRoute0 innerProfileRoute1 :
      InnerSplit → ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (innerWitness0 :
      (i : InnerSplit) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (innerProfileRoute0 i)))
    (innerWitness1 :
      (i : InnerSplit) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (innerProfileRoute1 i)))
    (hinnerLeft0 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (innerProfileRoute0 i))
          (innerWitness0 i) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hinnerRight0 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (innerProfileRoute0 i))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (innerProfileRoute0 i))) \
            innerWitness0 i) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hinnerLeft1 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (innerProfileRoute1 i))
          (innerWitness1 i) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hinnerRight1 :
      ∀ i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (innerProfileRoute1 i))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (innerProfileRoute1 i))) \
            innerWitness1 i) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hinnerInj0 : Set.InjOn innerProfileRoute0 innerSplit0)
    (hinnerInj1 : Set.InjOn innerProfileRoute1 innerSplit1)
    (hinnerDisj :
      ∀ i ∈ innerSplit0, ∀ j ∈ innerSplit1,
        innerProfileRoute0 i ≠ innerProfileRoute1 j)
    (hinnerPoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ∑ i ∈ innerSplit0,
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun
                (FK.boxGraph 3 (2 * n)) (innerProfileRoute0 i))) /
            384)
    (hinnerPoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ∑ i ∈ innerSplit1,
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun
                (FK.boxGraph 3 (2 * n)) (innerProfileRoute1 i))) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases
    edgeCopySourcePairData_twoRow_splitRoutes_of_sourceEquation_routes
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (B := (∅ : Finset (FK.boxVerts 3 (2 * n))))
      (β := β) (J := fun _ => (1 : ℝ))
      (split0 := emptySplit0) (split1 := emptySplit1)
      (F0 :=
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
          β n v w e0 m0)
      (F1 :=
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
          β n v w e0 m1)
      (profileRoute0 := emptyProfileRoute0)
      (profileRoute1 := emptyProfileRoute1)
      (witness0 := emptyWitness0) (witness1 := emptyWitness1)
      hemptyLeft0 hemptyRight0 hemptyLeft1 hemptyRight1
      hemptyInj0 hemptyInj1 hemptyDisj
      (by simpa [w] using hemptyPoint0)
      (by simpa [w] using hemptyPoint1) with
    ⟨emptyRoute0, emptyRoute1, hemptyDataInj0, hemptyDataInj1,
      hemptyDataDisj, hemptyDataPoint0, hemptyDataPoint1⟩
  rcases
    edgeCopySourcePairData_twoRow_splitRoutes_of_sourceEquation_routes
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n w)
      (B := doubledBoxInnerPairSource n v w)
      (β := β) (J := fun _ => (1 : ℝ))
      (split0 := innerSplit0) (split1 := innerSplit1)
      (F0 :=
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
          β n v w e0 m0)
      (F1 :=
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
          β n v w e0 m1)
      (profileRoute0 := innerProfileRoute0)
      (profileRoute1 := innerProfileRoute1)
      (witness0 := innerWitness0) (witness1 := innerWitness1)
      hinnerLeft0 hinnerRight0 hinnerLeft1 hinnerRight1
      hinnerInj0 hinnerInj1 hinnerDisj
      (by simpa [w] using hinnerPoint0)
      (by simpa [w] using hinnerPoint1) with
    ⟨innerRoute0, innerRoute1, hinnerDataInj0, hinnerDataInj1,
      hinnerDataDisj, hinnerDataPoint0, hinnerDataPoint1⟩
  exact
    exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt_of_cell_subset_pair_pointwise
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hcell_subset
      (EmptySplit := EmptySplit)
      emptySplit0 emptySplit1 emptyRoute0 emptyRoute1
      hemptyDataInj0 hemptyDataInj1 hemptyDataDisj
      (by simpa using hemptyDataPoint0)
      (by simpa using hemptyDataPoint1)
      (InnerSplit := InnerSplit)
      innerSplit0 innerSplit1 innerRoute0 innerRoute1
      hinnerDataInj0 hinnerDataInj1 hinnerDataDisj
      (by simpa using hinnerDataPoint0)
      (by simpa using hinnerDataPoint1)

set_option maxHeartbeats 500000 in


open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt_of_cell_subset_pair_emptySplits_nonpos
    {β : ℝ} {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 m1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hcell_subset :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      ∀ m : Profile,
        m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
          m ∈ ({m0, m1} : Finset Profile))
    (hemptyNonpos0 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤ 0)
    (hemptyNonpos1 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤ 0)
    (hinnerNonpos0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤ 0)
    (hinnerNonpos1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤ 0) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let emptyRoute :
      Empty →
        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    fun i => Empty.elim i
  let innerRoute :
      Empty →
        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) :=
    fun i => Empty.elim i
  exact
    exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt_of_cell_subset_pair_pointwise
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hcell_subset
      (EmptySplit := Empty)
      (emptySplit0 := (∅ : Finset Empty))
      (emptySplit1 := (∅ : Finset Empty))
      (emptyRoute0 := emptyRoute)
      (emptyRoute1 := emptyRoute)
      (hemptyInj0 := by intro i hi _j _hj _hroute; cases hi)
      (hemptyInj1 := by intro i hi _j _hj _hroute; cases hi)
      (hemptyDisj := by intro i hi _j _hj _hroute; cases hi)
      (hemptyPoint0 := by simpa [emptyRoute] using hemptyNonpos0)
      (hemptyPoint1 := by simpa [emptyRoute] using hemptyNonpos1)
      (InnerSplit := Empty)
      (innerSplit0 := (∅ : Finset Empty))
      (innerSplit1 := (∅ : Finset Empty))
      (innerRoute0 := innerRoute)
      (innerRoute1 := innerRoute)
      (hinnerInj0 := by intro i hi _j _hj _hroute; cases hi)
      (hinnerInj1 := by intro i hi _j _hj _hroute; cases hi)
      (hinnerDisj := by intro i hi _j _hj _hroute; cases hi)
      (hinnerPoint0 := by simpa [innerRoute] using hinnerNonpos0)
      (hinnerPoint1 := by simpa [innerRoute] using hinnerNonpos1)

end Exact3D
end StatMech
