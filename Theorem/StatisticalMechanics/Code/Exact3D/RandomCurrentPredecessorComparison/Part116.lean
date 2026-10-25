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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part108
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellRouteShareBoundsAt_of_coverRouteShareBoundsAt
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
    (hcover :
      ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew ∧
      ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt]
    at hcover
  rcases hcover with
    ⟨rows, hcell_subset,
      ⟨EmptySplit, emptySplitRows, emptyRouteRows, hemptyInj, hemptyPoint⟩,
      ⟨InnerSplit, innerSplitRows, innerRouteRows, hinnerInj, hinnerPoint⟩⟩
  constructor
  · exact
      exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt_of_cell_subset_finset
        (β := β) (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew) (rows := rows)
        hcell_subset emptySplitRows emptyRouteRows hemptyInj hemptyPoint
  · exact
      exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt_of_cell_subset_finset
        (β := β) (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew) (rows := rows)
        hcell_subset innerSplitRows innerRouteRows hinnerInj hinnerPoint

set_option maxHeartbeats 700000 in


open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt_of_cell_subset_finset_sourceEquation
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
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Profile := ↥G.edgeFinset → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases
    edgeCopySourcePairData_attach_splitRoutes_of_sourceEquation_routes_beta_div_six_div_384
      (G := G)
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (B := (∅ : Finset (FK.boxVerts 3 (2 * n))))
      (β := β) (J := fun _ => (1 : ℝ))
      (s := rows)
      (F := fun m : Profile =>
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
          β n v w e0 m)
      emptySplitRows emptyProfileRouteRows emptyWitnessRows
      (by simpa [G] using hemptyLeft)
      (by simpa [G] using hemptyRight)
      (by simpa [G] using hemptyInj)
      (by
        intro m
        simpa [G, w] using hemptyPoint m.1 m.2) with
    ⟨emptyRouteRows, hemptyDataInj, hemptyDataPoint⟩
  rcases
    edgeCopySourcePairData_attach_splitRoutes_of_sourceEquation_routes_beta_div_six_div_384
      (G := G)
      (A := doubledBoxOriginToInnerEndpointSource n w)
      (B := doubledBoxInnerPairSource n v w)
      (β := β) (J := fun _ => (1 : ℝ))
      (s := rows)
      (F := fun m : Profile =>
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
          β n v w e0 m)
      innerSplitRows innerProfileRouteRows innerWitnessRows
      (by simpa [G, w] using hinnerLeft)
      (by simpa [G, w] using hinnerRight)
      (by simpa [G] using hinnerInj)
      (by
        intro m
        simpa [G, w] using hinnerPoint m.1 m.2) with
    ⟨innerRouteRows, hinnerDataInj, hinnerDataPoint⟩
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt]
  refine ⟨rows, ?_, ?_, ?_⟩
  · simpa [G, w] using hcell_subset
  · refine ⟨EmptySplit, emptySplitRows, emptyRouteRows, ?_, ?_⟩
    · simpa [G] using hemptyDataInj
    · intro m hm
      simpa [G, w] using hemptyDataPoint m hm
  · refine ⟨InnerSplit, innerSplitRows, innerRouteRows, ?_, ?_⟩
    · simpa [G, w] using hinnerDataInj
    · intro m hm
      simpa [G, w] using hinnerDataPoint m hm

end Exact3D
end StatMech
