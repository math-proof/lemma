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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part110
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

open Classical in
set_option linter.style.longLine false in

@[simp]
theorem randomCurrent_sources_fluxEdgeCopyFinsetCast
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {m m' : ↥G.edgeFinset → ℕ} (hmm' : m = m')
    (K : Finset (Sharpness.FluxEdgeCopy.Copy G m)) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m')
        (fluxEdgeCopyFinsetCast hmm' K) =
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m) K := by
  cases hmm'
  rfl

open Classical in
set_option linter.style.longLine false in


@[simp]
theorem randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {m m' : ↥G.edgeFinset → ℕ} (hmm' : m = m')
    (K : Finset (Sharpness.FluxEdgeCopy.Copy G m)) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m')
        ((Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m')) \
          fluxEdgeCopyFinsetCast hmm' K) =
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        ((Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m)) \
          K) := by
  cases hmm'
  rfl

set_option maxHeartbeats 1000000 in


open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_subset_pair_sourceEquation_pointwise
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
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Profile := ↥G.edgeFinset → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let rows : Finset Profile := {m0, m1}
  let emptySplitRows : {m : Profile // m ∈ rows} → Finset EmptySplit :=
    fun m => if m.1 = m0 then emptySplit0 else emptySplit1
  let emptyProfileRouteRows :
      (m : {m : Profile // m ∈ rows}) → EmptySplit → Profile :=
    fun m i => if m.1 = m0 then emptyProfileRoute0 i else emptyProfileRoute1 i
  let emptyWitnessRows :
      (m : {m : Profile // m ∈ rows}) → (i : EmptySplit) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (emptyProfileRouteRows m i)) :=
    fun m i =>
      if hm0 : m.1 = m0 then
        fluxEdgeCopyFinsetCast
          (G := G)
          (m := emptyProfileRoute0 i)
          (m' := emptyProfileRouteRows m i)
          (by simp [emptyProfileRouteRows, hm0]) (emptyWitness0 i)
      else
        fluxEdgeCopyFinsetCast
          (G := G)
          (m := emptyProfileRoute1 i)
          (m' := emptyProfileRouteRows m i)
          (by simp [emptyProfileRouteRows, hm0]) (emptyWitness1 i)
  have hemptyInjRows :
      Set.InjOn
        (fun p :
            Sigma (fun _ : {m : Profile // m ∈ rows} => EmptySplit) =>
          emptyProfileRouteRows p.1 p.2)
        (rows.attach.sigma emptySplitRows) := by
    simpa [rows, emptySplitRows, emptyProfileRouteRows, G] using
      finset_pair_attach_sigma_if_route_injOn
        (m0 := m0) (m1 := m1)
        emptySplit0 emptySplit1 emptyProfileRoute0 emptyProfileRoute1
        hemptyInj0 hemptyInj1 hemptyDisj
  have hemptyLeftRows :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (emptyProfileRouteRows m i))
          (emptyWitnessRows m i) =
          doubledBoxOriginToInnerEndpointSource n v := by
    intro m i
    by_cases hm0 : m.1 = m0
    · dsimp only [emptyWitnessRows]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := G)
          (m := emptyProfileRoute0 i)
          (m' := emptyProfileRouteRows m i)
          (by simp [emptyProfileRouteRows, hm0]) (emptyWitness0 i)).trans
          (by simpa [G] using hemptyLeft0 i)
    · dsimp only [emptyWitnessRows]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := G)
          (m := emptyProfileRoute1 i)
          (m' := emptyProfileRouteRows m i)
          (by simp [emptyProfileRouteRows, hm0]) (emptyWitness1 i)).trans
          (by simpa [G] using hemptyLeft1 i)
  have hemptyRightRows :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (emptyProfileRouteRows m i))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy G
                  (emptyProfileRouteRows m i))) \
            emptyWitnessRows m i) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
    intro m i
    by_cases hm0 : m.1 = m0
    · dsimp only [emptyWitnessRows]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := G)
          (m := emptyProfileRoute0 i)
          (m' := emptyProfileRouteRows m i)
          (by simp [emptyProfileRouteRows, hm0]) (emptyWitness0 i)).trans
          (by simpa [G] using hemptyRight0 i)
    · dsimp only [emptyWitnessRows]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := G)
          (m := emptyProfileRoute1 i)
          (m' := emptyProfileRouteRows m i)
          (by simp [emptyProfileRouteRows, hm0]) (emptyWitness1 i)).trans
          (by simpa [G] using hemptyRight1 i)
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
    by_cases hm0 : m = m0
    · subst m
      simpa [emptySplitRows, emptyProfileRouteRows, G, w] using hemptyPoint0
    · have hm_pair : m ∈ ({m0, m1} : Finset Profile) := by
        simpa [rows] using hm
      have hm_or : m = m0 ∨ m = m1 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hm_pair
      have hm1 : m = m1 := hm_or.resolve_left hm0
      subst m
      simpa [emptySplitRows, emptyProfileRouteRows, G, w, hm0] using
        hemptyPoint1
  let innerSplitRows : {m : Profile // m ∈ rows} → Finset InnerSplit :=
    fun m => if m.1 = m0 then innerSplit0 else innerSplit1
  let innerProfileRouteRows :
      (m : {m : Profile // m ∈ rows}) → InnerSplit → Profile :=
    fun m i => if m.1 = m0 then innerProfileRoute0 i else innerProfileRoute1 i
  let innerWitnessRows :
      (m : {m : Profile // m ∈ rows}) → (i : InnerSplit) →
        Finset (Sharpness.FluxEdgeCopy.Copy G (innerProfileRouteRows m i)) :=
    fun m i =>
      if hm0 : m.1 = m0 then
        fluxEdgeCopyFinsetCast
          (G := G)
          (m := innerProfileRoute0 i)
          (m' := innerProfileRouteRows m i)
          (by simp [innerProfileRouteRows, hm0]) (innerWitness0 i)
      else
        fluxEdgeCopyFinsetCast
          (G := G)
          (m := innerProfileRoute1 i)
          (m' := innerProfileRouteRows m i)
          (by simp [innerProfileRouteRows, hm0]) (innerWitness1 i)
  have hinnerInjRows :
      Set.InjOn
        (fun p :
            Sigma (fun _ : {m : Profile // m ∈ rows} => InnerSplit) =>
          innerProfileRouteRows p.1 p.2)
        (rows.attach.sigma innerSplitRows) := by
    simpa [rows, innerSplitRows, innerProfileRouteRows, G] using
      finset_pair_attach_sigma_if_route_injOn
        (m0 := m0) (m1 := m1)
        innerSplit0 innerSplit1 innerProfileRoute0 innerProfileRoute1
        hinnerInj0 hinnerInj1 hinnerDisj
  have hinnerLeftRows :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (innerProfileRouteRows m i))
          (innerWitnessRows m i) =
          doubledBoxOriginToInnerEndpointSource n w := by
    intro m i
    by_cases hm0 : m.1 = m0
    · dsimp only [innerWitnessRows]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := G)
          (m := innerProfileRoute0 i)
          (m' := innerProfileRouteRows m i)
          (by simp [innerProfileRouteRows, hm0]) (innerWitness0 i)).trans
          (by simpa [G, w] using hinnerLeft0 i)
    · dsimp only [innerWitnessRows]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := G)
          (m := innerProfileRoute1 i)
          (m' := innerProfileRouteRows m i)
          (by simp [innerProfileRouteRows, hm0]) (innerWitness1 i)).trans
          (by simpa [G, w] using hinnerLeft1 i)
  have hinnerRightRows :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G (innerProfileRouteRows m i))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy G
                  (innerProfileRouteRows m i))) \
            innerWitnessRows m i) =
          doubledBoxInnerPairSource n v w := by
    intro m i
    by_cases hm0 : m.1 = m0
    · dsimp only [innerWitnessRows]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := G)
          (m := innerProfileRoute0 i)
          (m' := innerProfileRouteRows m i)
          (by simp [innerProfileRouteRows, hm0]) (innerWitness0 i)).trans
          (by simpa [G, w] using hinnerRight0 i)
    · dsimp only [innerWitnessRows]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := G)
          (m := innerProfileRoute1 i)
          (m' := innerProfileRouteRows m i)
          (by simp [innerProfileRouteRows, hm0]) (innerWitness1 i)).trans
          (by simpa [G, w] using hinnerRight1 i)
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
    by_cases hm0 : m = m0
    · subst m
      simpa [innerSplitRows, innerProfileRouteRows, G, w] using hinnerPoint0
    · have hm_pair : m ∈ ({m0, m1} : Finset Profile) := by
        simpa [rows] using hm
      have hm_or : m = m0 ∨ m = m1 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hm_pair
      have hm1 : m = m1 := hm_or.resolve_left hm0
      subst m
      simpa [innerSplitRows, innerProfileRouteRows, G, w, hm0] using
        hinnerPoint1
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt]
  refine ⟨rows, ?_, ?_, ?_⟩
  · simpa [rows, G, w] using hcell_subset
  · refine
      ⟨EmptySplit, emptySplitRows, emptyProfileRouteRows, emptyWitnessRows,
        ?_, ?_, hemptyInjRows, hemptyPointRows⟩
    · intro m i
      exact hemptyLeftRows m i
    · intro m i
      exact hemptyRightRows m i
  · refine
      ⟨InnerSplit, innerSplitRows, innerProfileRouteRows, innerWitnessRows,
        ?_, ?_, hinnerInjRows, hinnerPointRows⟩
    · intro m i
      exact hinnerLeftRows m i
    · intro m i
      exact hinnerRightRows m i

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_empty
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
    ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt
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
  have hfalse : ∀ m : {m : Profile // m ∈ cell}, False := by
    intro m
    have hmem : m.1 ∈ (∅ : Finset Profile) := by
      simpa [hcell] using m.2
    cases hmem
  let profileRoute : {m : Profile // m ∈ cell} → Profile :=
    fun m => False.elim (hfalse m)
  let witness :
      (m : {m : Profile // m ∈ cell}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRoute m)) :=
    fun m => False.elim (hfalse m)
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt]
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a _b _h
    exact False.elim (hfalse a)
  · intro m
    exact False.elim (hfalse m)
  · intro m
    exact False.elim (hfalse m)
  · intro m hm
    exact False.elim
      (hfalse ⟨m, by simpa [cell, Ωactive, w] using hm⟩)

open Classical in
set_option linter.style.longLine false in

theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_empty
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
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
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
  have hfalse : ∀ m : {m : Profile // m ∈ cell}, False := by
    intro m
    have hmem : m.1 ∈ (∅ : Finset Profile) := by
      simpa [hcell] using m.2
    cases hmem
  let profileRoute : {m : Profile // m ∈ cell} → Profile :=
    fun m => False.elim (hfalse m)
  let witness :
      (m : {m : Profile // m ∈ cell}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRoute m)) :=
    fun m => False.elim (hfalse m)
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt]
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a _b _h
    exact False.elim (hfalse a)
  · intro m
    exact False.elim (hfalse m)
  · intro m
    exact False.elim (hfalse m)
  · intro m hm
    exact False.elim
      (hfalse ⟨m, by simpa [cell, Ωactive, w] using hm⟩)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_singleton
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
    (hcell_singleton :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0})
    (profile0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (witness0 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile0))
    (hleft :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        witness0 =
        doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) profile0)) \
          witness0) =
        (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hpoint :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) profile0)) /
          384) :
    ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt
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
  have hcell : cell = {m0} := by
    simpa [cell, Ωactive, w] using hcell_singleton
  let profileRoute : {m : Profile // m ∈ cell} → Profile :=
    fun _ => profile0
  let witness :
      (m : {m : Profile // m ∈ cell}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRoute m)) :=
    fun _ => witness0
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt]
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a b _h
    apply Subtype.ext
    have ha : a.1 ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact a.2
    have hb : b.1 ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact b.2
    exact (Finset.mem_singleton.mp ha).trans
      (Finset.mem_singleton.mp hb).symm
  · intro m
    simpa [profileRoute, witness] using hleft
  · intro m
    simpa [profileRoute, witness] using hright
  · intro m hm
    have hm_singleton : m ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact hm
    have hm_eq : m = m0 := Finset.mem_singleton.mp hm_singleton
    subst m
    simpa [profileRoute, w] using hpoint

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_singleton
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
    (hcell_singleton :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0})
    (profile0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (witness0 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile0))
    (hleft :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        witness0 =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hright :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) profile0)) \
          witness0) =
        doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hpoint :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) profile0)) /
          384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
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
  have hcell : cell = {m0} := by
    simpa [cell, Ωactive, w] using hcell_singleton
  let profileRoute : {m : Profile // m ∈ cell} → Profile :=
    fun _ => profile0
  let witness :
      (m : {m : Profile // m ∈ cell}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRoute m)) :=
    fun _ => witness0
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt]
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a b _h
    apply Subtype.ext
    have ha : a.1 ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact a.2
    have hb : b.1 ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact b.2
    exact (Finset.mem_singleton.mp ha).trans
      (Finset.mem_singleton.mp hb).symm
  · intro m
    simpa [profileRoute, witness, w] using hleft
  · intro m
    simpa [profileRoute, witness, w] using hright
  · intro m hm
    have hm_singleton : m ∈ ({m0} : Finset Profile) := by
      rw [← hcell]
      exact hm
    have hm_eq : m = m0 := Finset.mem_singleton.mp hm_singleton
    subst m
    simpa [profileRoute, w] using hpoint

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairFiniteCell_mem_pair_cases_of_cell_eq_pair
    {n : ℕ}
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
    {m0 m1 m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hm :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      m ∈ Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)) :
    m = m0 ∨ m = m1 := by
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
  have hcell : cell = ({m0, m1} : Finset Profile) := by
    simpa [cell, Ωactive, w] using hcell_pair
  have hm_cell : m ∈ cell := by
    simpa [cell, Ωactive, w] using hm
  have hm_pair : m ∈ ({m0, m1} : Finset Profile) := by
    rw [← hcell]
    exact hm_cell
  simpa [Finset.mem_insert, Finset.mem_singleton] using hm_pair

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair
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
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (profile0 profile1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hprofile_ne : profile0 ≠ profile1)
    (witness0 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile0))
    (witness1 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile1))
    (hleft0 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        witness0 =
        doubledBoxOriginToInnerEndpointSource n v)
    (hleft1 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile1)
        witness1 =
        doubledBoxOriginToInnerEndpointSource n v)
    (hright0 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) profile0)) \
          witness0) =
        (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hright1 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile1)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) profile1)) \
          witness1) =
        (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) profile0)) /
          384)
    (hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) profile1)) /
          384) :
    ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt
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
  have hcell : cell = ({m0, m1} : Finset Profile) := by
    simpa [cell, Ωactive, w] using hcell_pair
  let profileRoute : {m : Profile // m ∈ cell} → Profile :=
    fun m => if m.1 = m0 then profile0 else profile1
  let witness :
      (m : {m : Profile // m ∈ cell}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRoute m)) :=
    fun m =>
      if hm0 : m.1 = m0 then
        fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile0) (m' := profileRoute m)
          (by simp [profileRoute, hm0]) witness0
      else
        fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile1) (m' := profileRoute m)
          (by simp [profileRoute, hm0]) witness1
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt]
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a b hroute
    apply Subtype.ext
    by_cases ha0 : a.1 = m0
    · by_cases hb0 : b.1 = m0
      · exact ha0.trans hb0.symm
      · have hpa : profileRoute a = profile0 := by
          dsimp [profileRoute]
          exact if_pos ha0
        have hpb : profileRoute b = profile1 := by
          dsimp [profileRoute]
          exact if_neg hb0
        have hp01 : profile0 = profile1 := by
          calc
            profile0 = profileRoute a := hpa.symm
            _ = profileRoute b := hroute
            _ = profile1 := hpb
        exact False.elim (hprofile_ne hp01)
    · by_cases hb0 : b.1 = m0
      · have hpa : profileRoute a = profile1 := by
          dsimp [profileRoute]
          exact if_neg ha0
        have hpb : profileRoute b = profile0 := by
          dsimp [profileRoute]
          exact if_pos hb0
        have hp10 : profile1 = profile0 := by
          calc
            profile1 = profileRoute a := hpa.symm
            _ = profileRoute b := hroute
            _ = profile0 := hpb
        exact False.elim (hprofile_ne hp10.symm)
      · have ha_pair : a.1 ∈ ({m0, m1} : Finset Profile) := by
          rw [← hcell]
          exact a.2
        have hb_pair : b.1 ∈ ({m0, m1} : Finset Profile) := by
          rw [← hcell]
          exact b.2
        have ha_or : a.1 = m0 ∨ a.1 = m1 := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using ha_pair
        have hb_or : b.1 = m0 ∨ b.1 = m1 := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using hb_pair
        exact (ha_or.resolve_left ha0).trans
          (hb_or.resolve_left hb0).symm
  · intro m
    by_cases hm0 : m.1 = m0
    · dsimp only [witness]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile0) (m' := profileRoute m)
          (by simp [profileRoute, hm0]) witness0).trans hleft0
    · dsimp only [witness]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile1) (m' := profileRoute m)
          (by simp [profileRoute, hm0]) witness1).trans hleft1
  · intro m
    by_cases hm0 : m.1 = m0
    · dsimp only [witness]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile0) (m' := profileRoute m)
          (by simp [profileRoute, hm0]) witness0).trans hright0
    · dsimp only [witness]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile1) (m' := profileRoute m)
          (by simp [profileRoute, hm0]) witness1).trans hright1
  · intro m hm
    by_cases hm0 : m = m0
    · subst m
      simpa [profileRoute, w] using hpoint0
    · have hm_pair : m ∈ ({m0, m1} : Finset Profile) := by
        rw [← hcell]
        exact hm
      have hm_or : m = m0 ∨ m = m1 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hm_pair
      have hm1 : m = m1 := hm_or.resolve_left hm0
      subst m
      simpa [profileRoute, w, hm0] using hpoint1

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hm01 : m0 ≠ m1)
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m1)) /
          384)
    (hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m0)) /
          384) :
    ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt
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
  have hcell : cell = ({m0, m1} : Finset Profile) := by
    simpa [cell, Ωactive, w] using hcell_pair
  have hm0_cell : m0 ∈ cell := by
    rw [hcell]
    simp
  have hm1_cell : m1 ∈ cell := by
    rw [hcell]
    simp
  have hm0_filter :
      m0 ∈ Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) := by
    simpa [cell] using hm0_cell
  have hm1_filter :
      m1 ∈ Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) := by
    simpa [cell] using hm1_cell
  have hm0_Ωactive : m0 ∈ Ωactive := (Finset.mem_filter.mp hm0_filter).1
  have hm1_Ωactive : m1 ∈ Ωactive := (Finset.mem_filter.mp hm1_filter).1
  have hm0_owner : doubledBoxOriginIncidentOwner n m0 = some ew :=
    (Finset.mem_filter.mp hm0_filter).2.2
  have hm1_owner : doubledBoxOriginIncidentOwner n m1 = some ew :=
    (Finset.mem_filter.mp hm1_filter).2.2
  have hm0_active : doubledBoxIncrementedFullSourceActive n w e0 m0 := by
    simpa [Ωactive] using (Finset.mem_filter.mp hm0_Ωactive).2
  have hm1_active : doubledBoxIncrementedFullSourceActive n w e0 m1 := by
    simpa [Ωactive] using (Finset.mem_filter.mp hm1_Ωactive).2
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_switched_emptySourceEquations_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m1) hedge (by simpa [w] using hm1_active) hm1_owner with
    ⟨profile1Source, witness1Source, hprofile1Source, hleft1Source,
      hright1Source⟩
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_switched_emptySourceEquations_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m0) hedge (by simpa [w] using hm0_active) hm0_owner with
    ⟨profile0Source, witness0Source, hprofile0Source, hleft0Source,
      hright0Source⟩
  have hprofile_ne : profile1Source ≠ profile0Source := by
    intro hprofile
    apply hm01
    calc
      m0 = profile0Source := hprofile0Source.symm
      _ = profile1Source := hprofile.symm
      _ = m1 := hprofile1Source
  exact
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hcell_pair
      profile1Source profile0Source hprofile_ne
      witness1Source witness0Source
      hleft1Source hleft0Source
      hright1Source hright0Source
      (by simpa [hprofile1Source, w] using hpoint0)
      (by simpa [hprofile0Source, w] using hpoint1)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_pairPointwise
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hm01 : m0 ≠ m1)
    (hpoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  have hm0_mem :
      m0 ∈ ({m0, m1} :
        Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) := by
    simp
  have hm1_mem :
      m1 ∈ ({m0, m1} :
        Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) := by
    simp
  have hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m1)) /
          384 := by
    simpa [hm01] using hpoint m0 hm0_mem
  have hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m0)) /
          384 := by
    simpa [hm01.symm] using hpoint m1 hm1_mem
  exact
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01 hpoint0 hpoint1

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair
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
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (profile0 profile1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hprofile_ne : profile0 ≠ profile1)
    (witness0 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile0))
    (witness1 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile1))
    (hleft0 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        witness0 =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hleft1 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile1)
        witness1 =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hright0 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) profile0)) \
          witness0) =
        doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hright1 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile1)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) profile1)) \
          witness1) =
        doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) profile0)) /
          384)
    (hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) profile1)) /
          384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
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
  have hcell : cell = ({m0, m1} : Finset Profile) := by
    simpa [cell, Ωactive, w] using hcell_pair
  let profileRoute : {m : Profile // m ∈ cell} → Profile :=
    fun m => if m.1 = m0 then profile0 else profile1
  let witness :
      (m : {m : Profile // m ∈ cell}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRoute m)) :=
    fun m =>
      if hm0 : m.1 = m0 then
        fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile0) (m' := profileRoute m)
          (by simp [profileRoute, hm0]) witness0
      else
        fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile1) (m' := profileRoute m)
          (by simp [profileRoute, hm0]) witness1
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt]
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a b hroute
    apply Subtype.ext
    by_cases ha0 : a.1 = m0
    · by_cases hb0 : b.1 = m0
      · exact ha0.trans hb0.symm
      · have hpa : profileRoute a = profile0 := by
          dsimp [profileRoute]
          exact if_pos ha0
        have hpb : profileRoute b = profile1 := by
          dsimp [profileRoute]
          exact if_neg hb0
        have hp01 : profile0 = profile1 := by
          calc
            profile0 = profileRoute a := hpa.symm
            _ = profileRoute b := hroute
            _ = profile1 := hpb
        exact False.elim (hprofile_ne hp01)
    · by_cases hb0 : b.1 = m0
      · have hpa : profileRoute a = profile1 := by
          dsimp [profileRoute]
          exact if_neg ha0
        have hpb : profileRoute b = profile0 := by
          dsimp [profileRoute]
          exact if_pos hb0
        have hp10 : profile1 = profile0 := by
          calc
            profile1 = profileRoute a := hpa.symm
            _ = profileRoute b := hroute
            _ = profile0 := hpb
        exact False.elim (hprofile_ne hp10.symm)
      · have ha_pair : a.1 ∈ ({m0, m1} : Finset Profile) := by
          rw [← hcell]
          exact a.2
        have hb_pair : b.1 ∈ ({m0, m1} : Finset Profile) := by
          rw [← hcell]
          exact b.2
        have ha_or : a.1 = m0 ∨ a.1 = m1 := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using ha_pair
        have hb_or : b.1 = m0 ∨ b.1 = m1 := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using hb_pair
        exact (ha_or.resolve_left ha0).trans
          (hb_or.resolve_left hb0).symm
  · intro m
    by_cases hm0 : m.1 = m0
    · dsimp only [witness]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile0) (m' := profileRoute m)
          (by simp [profileRoute, hm0]) witness0).trans hleft0
    · dsimp only [witness]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile1) (m' := profileRoute m)
          (by simp [profileRoute, hm0]) witness1).trans hleft1
  · intro m
    by_cases hm0 : m.1 = m0
    · dsimp only [witness]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile0) (m' := profileRoute m)
          (by simp [profileRoute, hm0]) witness0).trans hright0
    · dsimp only [witness]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile1) (m' := profileRoute m)
          (by simp [profileRoute, hm0]) witness1).trans hright1
  · intro m hm
    by_cases hm0 : m = m0
    · subst m
      simpa [profileRoute, w] using hpoint0
    · have hm_pair : m ∈ ({m0, m1} : Finset Profile) := by
        rw [← hcell]
        exact hm
      have hm_or : m = m0 ∨ m = m1 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hm_pair
      have hm1 : m = m1 := hm_or.resolve_left hm0
      subst m
      simpa [profileRoute, w, hm0] using hpoint1

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedInCurrentSelectedDeletion
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    {p0 : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) (Function.update m0 e0 (m0 e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m0 e0 (m0 e0 + 1)))}
    {p1 : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) (Function.update m1 e0 (m1 e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m1 e0 (m1 e0 + 1)))}
    (hp0 :
      p0 ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m0 e0 (m0 e0 + 1)) e0)
    (hp1 :
      p1 ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m1 e0 (m1 e0 + 1)) e0)
    (hprofile_ne :
      Function.update (Function.update m1 e0 (m1 e0 + 1)) p1.2.1
          ((Function.update m1 e0 (m1 e0 + 1)) p1.2.1 - 1) ≠
        Function.update (Function.update m0 e0 (m0 e0 + 1)) p0.2.1
          ((Function.update m0 e0 (m0 e0 + 1)) p0.2.1 - 1))
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update (Function.update m1 e0 (m1 e0 + 1)) p1.2.1
                ((Function.update m1 e0 (m1 e0 + 1)) p1.2.1 - 1)))) /
          384)
    (hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update (Function.update m0 e0 (m0 e0 + 1)) p0.2.1
                ((Function.update m0 e0 (m0 e0 + 1)) p0.2.1 - 1)))) /
          384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
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
  have hcell : cell = ({m0, m1} : Finset Profile) := by
    simpa [cell, Ωactive, w] using hcell_pair
  have hm0_cell : m0 ∈ cell := by
    rw [hcell]
    simp
  have hm1_cell : m1 ∈ cell := by
    rw [hcell]
    simp
  have hm0_filter :
      m0 ∈ Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) := by
    simpa [cell] using hm0_cell
  have hm1_filter :
      m1 ∈ Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) := by
    simpa [cell] using hm1_cell
  have hm0_Ωactive : m0 ∈ Ωactive := (Finset.mem_filter.mp hm0_filter).1
  have hm1_Ωactive : m1 ∈ Ωactive := (Finset.mem_filter.mp hm1_filter).1
  have hm0_active : doubledBoxIncrementedFullSourceActive n w e0 m0 := by
    simpa [Ωactive] using (Finset.mem_filter.mp hm0_Ωactive).2
  have hm1_active : doubledBoxIncrementedFullSourceActive n w e0 m1 := by
    simpa [Ωactive] using (Finset.mem_filter.mp hm1_Ωactive).2
  rcases
      doubledBoxIncrementedFullSourceActive_inCurrentSelectedDeletion_switched_innerPairSourceEquations_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m1)
        hedge (by simpa [w] using hm1_active) (p := p1) hp1 with
    ⟨profile1Source, witness1Source, hprofile1Source, hleft1Source,
      hright1Source⟩
  rcases
      doubledBoxIncrementedFullSourceActive_inCurrentSelectedDeletion_switched_innerPairSourceEquations_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m0)
        hedge (by simpa [w] using hm0_active) (p := p0) hp0 with
    ⟨profile0Source, witness0Source, hprofile0Source, hleft0Source,
      hright0Source⟩
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hcell_pair
      profile1Source profile0Source
      (by
        intro hprofile
        exact hprofile_ne
          (by
            calc
              Function.update (Function.update m1 e0 (m1 e0 + 1)) p1.2.1
                  ((Function.update m1 e0 (m1 e0 + 1)) p1.2.1 - 1) =
                    profile1Source := hprofile1Source.symm
              _ = profile0Source := hprofile
              _ =
                  Function.update (Function.update m0 e0 (m0 e0 + 1)) p0.2.1
                    ((Function.update m0 e0 (m0 e0 + 1)) p0.2.1 - 1) :=
                hprofile0Source))
      witness1Source witness0Source
      hleft1Source hleft0Source
      hright1Source hright0Source
      (by simpa [hprofile1Source, w] using hpoint0)
      (by simpa [hprofile0Source, w] using hpoint1)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedInCurrentSelectedDeletion_rowProfile
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    {p0 : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) (Function.update m0 e0 (m0 e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m0 e0 (m0 e0 + 1)))}
    {p1 : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) (Function.update m1 e0 (m1 e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m1 e0 (m1 e0 + 1)))}
    (hp0 :
      p0 ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m0 e0 (m0 e0 + 1)) e0)
    (hp1 :
      p1 ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m1 e0 (m1 e0 + 1)) e0)
    (hm01 : m0 ≠ m1)
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m1)) /
          384)
    (hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m0)) /
          384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
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
  have hcell : cell = ({m0, m1} : Finset Profile) := by
    simpa [cell, Ωactive, w] using hcell_pair
  have hm0_cell : m0 ∈ cell := by
    rw [hcell]
    simp
  have hm1_cell : m1 ∈ cell := by
    rw [hcell]
    simp
  have hm0_filter :
      m0 ∈ Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) := by
    simpa [cell] using hm0_cell
  have hm1_filter :
      m1 ∈ Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) := by
    simpa [cell] using hm1_cell
  have hm0_Ωactive : m0 ∈ Ωactive := (Finset.mem_filter.mp hm0_filter).1
  have hm1_Ωactive : m1 ∈ Ωactive := (Finset.mem_filter.mp hm1_filter).1
  have hm0_active : doubledBoxIncrementedFullSourceActive n w e0 m0 := by
    simpa [Ωactive] using (Finset.mem_filter.mp hm0_Ωactive).2
  have hm1_active : doubledBoxIncrementedFullSourceActive n w e0 m1 := by
    simpa [Ωactive] using (Finset.mem_filter.mp hm1_Ωactive).2
  rcases
      doubledBoxIncrementedFullSourceActive_inCurrentSelectedDeletion_switched_innerPairSourceEquations_profile_eq_row_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m1)
        hedge (by simpa [w] using hm1_active) (p := p1) hp1 with
    ⟨profile1Source, witness1Source, hprofile1Source, hleft1Source,
      hright1Source⟩
  rcases
      doubledBoxIncrementedFullSourceActive_inCurrentSelectedDeletion_switched_innerPairSourceEquations_profile_eq_row_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m0)
        hedge (by simpa [w] using hm0_active) (p := p0) hp0 with
    ⟨profile0Source, witness0Source, hprofile0Source, hleft0Source,
      hright0Source⟩
  have hprofile_ne : profile1Source ≠ profile0Source := by
    intro hprofile
    apply hm01
    calc
      m0 = profile0Source := hprofile0Source.symm
      _ = profile1Source := hprofile.symm
      _ = m1 := hprofile1Source
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hcell_pair
      profile1Source profile0Source hprofile_ne
      witness1Source witness0Source
      hleft1Source hleft0Source
      hright1Source hright0Source
      (by simpa [hprofile1Source, w] using hpoint0)
      (by simpa [hprofile0Source, w] using hpoint1)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedInCurrentSelectedDeletion_rowProfile_of_inCurrent_nonempty
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hp0_nonempty :
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m0 e0 (m0 e0 + 1)) e0).Nonempty)
    (hp1_nonempty :
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m1 e0 (m1 e0 + 1)) e0).Nonempty)
    (hm01 : m0 ≠ m1)
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m1)) /
          384)
    (hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m0)) /
          384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  rcases hp0_nonempty with ⟨p0, hp0⟩
  rcases hp1_nonempty with ⟨p1, hp1⟩
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedInCurrentSelectedDeletion_rowProfile
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair
      (p0 := p0) (p1 := p1) hp0 hp1 hm01 hpoint0 hpoint1

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedInCurrentSelectedDeletion_rowProfile_of_inCurrent_card_pos
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hp0_card :
      0 <
        (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m0 e0 (m0 e0 + 1)) e0).card)
    (hp1_card :
      0 <
        (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m1 e0 (m1 e0 + 1)) e0).card)
    (hm01 : m0 ≠ m1)
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m1)) /
          384)
    (hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m0)) /
          384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedInCurrentSelectedDeletion_rowProfile_of_inCurrent_nonempty
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair
      (Finset.card_pos.mp hp0_card) (Finset.card_pos.mp hp1_card)
      hm01 hpoint0 hpoint1

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedInCurrentSelectedDeletion_rowProfile_of_pair_inCurrent_card_pos_pointwise
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hm01 : m0 ≠ m1)
    (hinCurrent :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        0 <
          (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card)
    (hpoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  have hm0_mem :
      m0 ∈ ({m0, m1} :
        Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) := by
    simp
  have hm1_mem :
      m1 ∈ ({m0, m1} :
        Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) := by
    simp
  have hp0_card := hinCurrent m0 hm0_mem
  have hp1_card := hinCurrent m1 hm1_mem
  have hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m1)) /
          384 := by
    simpa [hm01] using hpoint m0 hm0_mem
  have hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m0)) /
          384 := by
    simpa [hm01.symm] using hpoint m1 hm1_mem
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedInCurrentSelectedDeletion_rowProfile_of_inCurrent_card_pos
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair
      hp0_card hp1_card hm01 hpoint0 hpoint1

set_option maxHeartbeats 900000 in


open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    {p0 : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) (Function.update m0 e0 (m0 e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m0 e0 (m0 e0 + 1)))}
    {p1 : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) (Function.update m1 e0 (m1 e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m1 e0 (m1 e0 + 1)))}
    (hp0 :
      p0 ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
        (Function.update m0 e0 (m0 e0 + 1)) e0)
    (hp1 :
      p1 ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
        (Function.update m1 e0 (m1 e0 + 1)) e0)
    (hprofile_ne :
      Function.update (Function.update m1 e0 (m1 e0 + 1)) p1.2.1
          ((Function.update m1 e0 (m1 e0 + 1)) p1.2.1 - 1) ≠
        Function.update (Function.update m0 e0 (m0 e0 + 1)) p0.2.1
          ((Function.update m0 e0 (m0 e0 + 1)) p0.2.1 - 1))
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update (Function.update m1 e0 (m1 e0 + 1)) p1.2.1
                ((Function.update m1 e0 (m1 e0 + 1)) p1.2.1 - 1)))) /
          384)
    (hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update (Function.update m0 e0 (m0 e0 + 1)) p0.2.1
                ((Function.update m0 e0 (m0 e0 + 1)) p0.2.1 - 1)))) /
          384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  have hcell : cell = ({m0, m1} : Finset Profile) := by
    simpa [cell, Ωactive, w, G] using hcell_pair
  have hm0_cell : m0 ∈ cell := by
    rw [hcell]
    simp
  have hm1_cell : m1 ∈ cell := by
    rw [hcell]
    simp
  have hm0_filter :
      m0 ∈ Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) := by
    simpa [cell] using hm0_cell
  have hm1_filter :
      m1 ∈ Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) := by
    simpa [cell] using hm1_cell
  have hm0_Ωactive : m0 ∈ Ωactive := (Finset.mem_filter.mp hm0_filter).1
  have hm1_Ωactive : m1 ∈ Ωactive := (Finset.mem_filter.mp hm1_filter).1
  have hm0_active : doubledBoxIncrementedFullSourceActive n w e0 m0 := by
    simpa [Ωactive] using (Finset.mem_filter.mp hm0_Ωactive).2
  have hm1_active : doubledBoxIncrementedFullSourceActive n w e0 m1 := by
    simpa [Ωactive] using (Finset.mem_filter.mp hm1_Ωactive).2
  have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w := by
    simpa [w] using
      boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos
  have hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v := by
    simpa [w] using
      boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos
  have hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) := by
    simpa [w] using
      boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
        (by omega : n ≤ 2 * n) v hvwedge hlt hypos
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        (n := n) (v := v) (w := w) hvwedge hwwedge hheight hadj with
    ⟨_edge, _hedge, hov, how, hvw⟩
  let M0 : ↥G.edgeFinset → ℕ := Function.update m0 e0 (m0 e0 + 1)
  let M1 : ↥G.edgeFinset → ℕ := Function.update m1 e0 (m1 e0 + 1)
  let profile0Source : ↥G.edgeFinset → ℕ :=
    Function.update M0 p0.2.1 (M0 p0.2.1 - 1)
  let profile1Source : ↥G.edgeFinset → ℕ :=
    Function.update M1 p1.2.1 (M1 p1.2.1 - 1)
  let witness0Source :
      Finset (Sharpness.FluxEdgeCopy.Copy G profile0Source) :=
    (Finset.univ :
        Finset (Sharpness.FluxEdgeCopy.Copy G profile0Source)) \
      copyDeletePreimageDecrementEraseFinset G M0 p0.2 p0.1
  let witness1Source :
      Finset (Sharpness.FluxEdgeCopy.Copy G profile1Source) :=
    (Finset.univ :
        Finset (Sharpness.FluxEdgeCopy.Copy G profile1Source)) \
      copyDeletePreimageDecrementEraseFinset G M1 p1.2 p1.1
  have hfull0 :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G M0)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G M0)) =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa [G, M0, w] using hm0_active
  have hfull1 :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G M1)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G M1)) =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa [G, M1, w] using hm1_active
  have hsrc0 :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementSourceEquations
      (n := n) (v := v) (w := w) M0 e0 (by simpa [w] using hedge)
      hfull0 hov how hvw (p := p0) (by simpa [G, M0, w] using hp0)
  have hsrc1 :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_swapped_decrementSourceEquations
      (n := n) (v := v) (w := w) M1 e0 (by simpa [w] using hedge)
      hfull1 hov how hvw (p := p1) (by simpa [G, M1, w] using hp1)
  have hleft0Source :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G profile0Source)
          witness0Source =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa only [G, M0, profile0Source, witness0Source, w] using hsrc0.1
  have hright0Source :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G profile0Source)
          ((Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy G profile0Source)) \
            witness0Source) =
        doubledBoxInnerPairSource n v w := by
    simpa only [G, M0, profile0Source, witness0Source, w] using hsrc0.2
  have hleft1Source :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G profile1Source)
          witness1Source =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa only [G, M1, profile1Source, witness1Source, w] using hsrc1.1
  have hright1Source :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G profile1Source)
          ((Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy G profile1Source)) \
            witness1Source) =
        doubledBoxInnerPairSource n v w := by
    simpa only [G, M1, profile1Source, witness1Source, w] using hsrc1.2
  have hprofile_ne' : profile1Source ≠ profile0Source := by
    simpa [G, M0, M1, profile0Source, profile1Source] using hprofile_ne
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hcell_pair
      profile1Source profile0Source hprofile_ne'
      witness1Source witness0Source
      hleft1Source hleft0Source
      hright1Source hright0Source
      (by simpa [G, M1, profile1Source, w] using hpoint0)
      (by simpa [G, M0, profile0Source, w] using hpoint1)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    {p0 : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) (Function.update m0 e0 (m0 e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m0 e0 (m0 e0 + 1)))}
    {p1 : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) (Function.update m1 e0 (m1 e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m1 e0 (m1 e0 + 1)))}
    (hp0 :
      p0 ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
        (Function.update m0 e0 (m0 e0 + 1)) e0)
    (hp1 :
      p1 ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
        (Function.update m1 e0 (m1 e0 + 1)) e0)
    (hm01 : m0 ≠ m1)
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m1)) /
          384)
    (hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m0)) /
          384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let M0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update m0 e0 (m0 e0 + 1)
  let M1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update m1 e0 (m1 e0 + 1)
  let profile0Source : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update M0 p0.2.1 (M0 p0.2.1 - 1)
  let profile1Source : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update M1 p1.2.1 (M1 p1.2.1 - 1)
  have hprofile0Source : profile0Source = m0 := by
    simpa [profile0Source, M0, w] using
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_decrement_increment_profile_eq
        (G := FK.boxGraph 3 (2 * n))
        (A := doubledBoxInnerPairSource n v w)
        (e0 := e0) (m := m0) (p := p0) (by simpa [w] using hp0)
  have hprofile1Source : profile1Source = m1 := by
    simpa [profile1Source, M1, w] using
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_decrement_increment_profile_eq
        (G := FK.boxGraph 3 (2 * n))
        (A := doubledBoxInnerPairSource n v w)
        (e0 := e0) (m := m1) (p := p1) (by simpa [w] using hp1)
  have hprofile_ne : profile1Source ≠ profile0Source := by
    intro hprofile
    apply hm01
    calc
      m0 = profile0Source := hprofile0Source.symm
      _ = profile1Source := hprofile.symm
      _ = m1 := hprofile1Source
  have hpoint0raw :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) profile1Source)) /
          384 := by
    simpa [hprofile1Source] using hpoint0
  have hpoint1raw :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) profile0Source)) /
          384 := by
    simpa [hprofile0Source] using hpoint1
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair
      (p0 := p0) (p1 := p1) hp0 hp1
      (by simpa [profile0Source, profile1Source, M0, M1] using hprofile_ne)
      (by simpa [profile1Source, M1] using hpoint0raw)
      (by simpa [profile0Source, M0] using hpoint1raw)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile_of_outsideCurrent_nonempty
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hp0_nonempty :
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
        (Function.update m0 e0 (m0 e0 + 1)) e0).Nonempty)
    (hp1_nonempty :
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
        (Function.update m1 e0 (m1 e0 + 1)) e0).Nonempty)
    (hm01 : m0 ≠ m1)
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m1)) /
          384)
    (hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m0)) /
          384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  rcases hp0_nonempty with ⟨p0, hp0⟩
  rcases hp1_nonempty with ⟨p1, hp1⟩
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair
      (p0 := p0) (p1 := p1) hp0 hp1 hm01 hpoint0 hpoint1

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile_of_outsideCurrent_card_pos
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hp0_card :
      0 <
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (Function.update m0 e0 (m0 e0 + 1)) e0).card)
    (hp1_card :
      0 <
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (Function.update m1 e0 (m1 e0 + 1)) e0).card)
    (hm01 : m0 ≠ m1)
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m1)) /
          384)
    (hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m0)) /
          384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile_of_outsideCurrent_nonempty
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair
      (Finset.card_pos.mp hp0_card) (Finset.card_pos.mp hp1_card)
      hm01 hpoint0 hpoint1

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile_of_pair_outsideCurrent_card_pos_pointwise
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hm01 : m0 ≠ m1)
    (houtsideCurrent :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        0 <
          (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxInnerPairSource n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            (Function.update m e0 (m e0 + 1)) e0).card)
    (hpoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  have hm0_mem :
      m0 ∈ ({m0, m1} :
        Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) := by
    simp
  have hm1_mem :
      m1 ∈ ({m0, m1} :
        Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) := by
    simp
  have hp0_card := houtsideCurrent m0 hm0_mem
  have hp1_card := houtsideCurrent m1 hm1_mem
  have hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m1)) /
          384 := by
    simpa [hm01] using hpoint m0 hm0_mem
  have hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m0)) /
          384 := by
    simpa [hm01.symm] using hpoint m1 hm1_mem
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile_of_outsideCurrent_card_pos
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair
      hp0_card hp1_card hm01 hpoint0 hpoint1

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile_of_selectedEdge_pos_pointwise
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hm01 : m0 ≠ m1)
    (hselectedEdge_pos :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        0 < m e0)
    (hpoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile_of_pair_outsideCurrent_card_pos_pointwise
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01
      (fun m hm =>
        doubledBoxInnerPairSourceSelectedEdgeOutsideCurrent_card_pos_of_strictSectorYPredecessor3_of_selectedEdge_pos
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
          hedge (hselectedEdge_pos m hm))
      hpoint

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile_of_selectedEdge_pos_or_zero_excluding_incrementInserted_card_pos_pointwise
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hm01 : m0 ≠ m1)
    (hbranch :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        0 < m e0 ∨
          m e0 = 0 ∧
            0 <
              (edgeCopySourceSectorExcludingCopy
                (FK.boxGraph 3 (2 * n))
                (doubledBoxInnerPairSource n v
                  (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                (Function.update m e0 (m e0 + 1))
                (edgeCopyIncrementInserted
                  (FK.boxGraph 3 (2 * n)) m e0)).card)
    (hpoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile_of_pair_outsideCurrent_card_pos_pointwise
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01
      (fun m hm => by
        rcases hbranch m hm with hmpos | hzero
        · exact
            doubledBoxInnerPairSourceSelectedEdgeOutsideCurrent_card_pos_of_strictSectorYPredecessor3_of_selectedEdge_pos
              (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
              (m := m) hedge hmpos
        · rcases hzero with ⟨hmzero, hexcluding⟩
          have hcard :=
            edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_card_eq_excluding_incrementInserted_card_of_update_zero
              (FK.boxGraph 3 (2 * n))
              (doubledBoxInnerPairSource n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              m e0 hmzero
          rwa [hcard])
      hpoint

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile_of_selectedEdge_pos_or_zero_containing_incrementInserted_card_pos_pointwise
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hm01 : m0 ≠ m1)
    (hbranch :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        0 < m e0 ∨
          m e0 = 0 ∧
            0 <
              (edgeCopySourceSectorContainingCopy
                (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n v)
                (Function.update m e0 (m e0 + 1))
                (edgeCopyIncrementInserted
                  (FK.boxGraph 3 (2 * n)) m e0)).card)
    (hpoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
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
  have hcell : cell = ({m0, m1} : Finset Profile) := by
    simpa [cell, Ωactive, w] using hcell_pair
  have hactive_of_pair :
      ∀ m ∈ ({m0, m1} : Finset Profile),
        doubledBoxIncrementedFullSourceActive n w e0 m := by
    intro m hm
    have hmcell : m ∈ cell := by
      rw [hcell]
      exact hm
    have hmfilter :
        m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) := by
      simpa [cell] using hmcell
    have hmΩactive : m ∈ Ωactive := (Finset.mem_filter.mp hmfilter).1
    exact (Finset.mem_filter.mp (by simpa [Ωactive] using hmΩactive)).2
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile_of_selectedEdge_pos_or_zero_excluding_incrementInserted_card_pos_pointwise
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01
      (fun m hm => by
        rcases hbranch m hm with hmpos | hzero
        · exact Or.inl hmpos
        · rcases hzero with ⟨hmzero, hcontaining⟩
          refine Or.inr ⟨hmzero, ?_⟩
          have hiff :=
            doubledBoxInnerPairSource_excluding_incrementInserted_card_pos_iff_switchedSource_containing_incrementInserted_card_pos_of_strictSectorYPredecessor3
              (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
              (m := m) hedge (by simpa [w] using hactive_of_pair m hm)
          exact hiff.mpr (by simpa [w] using hcontaining))
      hpoint

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile_of_selectedEdge_pos_or_zero_outsideCurrent_nonexhaustion_pointwise
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hm01 : m0 ≠ m1)
    (hbranch :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        0 < m e0 ∨
          m e0 = 0 ∧
            (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
                (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n v)
                (Function.update m e0 (m e0 + 1)) e0).card <
              (edgeCopySourceSectorSelectedEdgeCopyPairs
                (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n v)
                (Function.update m e0 (m e0 + 1)) e0).card)
    (hpoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
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
  have hcell : cell = ({m0, m1} : Finset Profile) := by
    simpa [cell, Ωactive, w] using hcell_pair
  have hactive_of_pair :
      ∀ m ∈ ({m0, m1} : Finset Profile),
        doubledBoxIncrementedFullSourceActive n w e0 m := by
    intro m hm
    have hmcell : m ∈ cell := by
      rw [hcell]
      exact hm
    have hmfilter :
        m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) := by
      simpa [cell] using hmcell
    have hmΩactive : m ∈ Ωactive := (Finset.mem_filter.mp hmfilter).1
    exact (Finset.mem_filter.mp (by simpa [Ωactive] using hmΩactive)).2
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_rowProfile_of_pair_outsideCurrent_card_pos_pointwise
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01
      (fun m hm => by
        rcases hbranch m hm with hmpos | hzero
        · exact
            doubledBoxInnerPairSourceSelectedEdgeOutsideCurrent_card_pos_of_strictSectorYPredecessor3_of_selectedEdge_pos
              (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
              (m := m) hedge hmpos
        · rcases hzero with ⟨hmzero, hstrict⟩
          exact
            doubledBoxInnerPairSourceSelectedEdgeOutsideCurrent_card_pos_of_strictSectorYPredecessor3_of_update_zero_outsideCurrent_card_lt_selectedEdgeCopyPairs_card
              (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
              (m := m) hedge (by simpa [w] using hactive_of_pair m hm)
              hmzero hstrict)
      hpoint

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_incrementedWeightPayment
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    {p0 : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) (Function.update m0 e0 (m0 e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m0 e0 (m0 e0 + 1)))}
    {p1 : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) (Function.update m1 e0 (m1 e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m1 e0 (m1 e0 + 1)))}
    (hp0 :
      p0 ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
        (Function.update m0 e0 (m0 e0 + 1)) e0)
    (hp1 :
      p1 ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
        (Function.update m1 e0 (m1 e0 + 1)) e0)
    (hprofile_ne :
      Function.update (Function.update m1 e0 (m1 e0 + 1)) p1.2.1
          ((Function.update m1 e0 (m1 e0 + 1)) p1.2.1 - 1) ≠
        Function.update (Function.update m0 e0 (m0 e0 + 1)) p0.2.1
          ((Function.update m0 e0 (m0 e0 + 1)) p0.2.1 - 1))
    (hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        (((1 : ℝ) / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m1 e0 (m1 e0 + 1)))) /
          384)
    (hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        (((1 : ℝ) / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m0 e0 (m0 e0 + 1)))) /
          384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  have hpay0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update (Function.update m1 e0 (m1 e0 + 1)) p1.2.1
                ((Function.update m1 e0 (m1 e0 + 1)) p1.2.1 - 1)))) /
          384 := by
    exact hpoint0.trans
      (doubledBox_selectedEdgeCopy_weight_div_six_div_384_le_beta_div_six_decrement
        (β := β) (n := n) hβ (Function.update m1 e0 (m1 e0 + 1)) p1.2)
  have hpay1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        ((β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update (Function.update m0 e0 (m0 e0 + 1)) p0.2.1
                ((Function.update m0 e0 (m0 e0 + 1)) p0.2.1 - 1)))) /
          384 := by
    exact hpoint1.trans
      (doubledBox_selectedEdgeCopy_weight_div_six_div_384_le_beta_div_six_decrement
        (β := β) (n := n) hβ (Function.update m0 e0 (m0 e0 + 1)) p0.2)
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair
      (p0 := p0) (p1 := p1) hp0 hp1 hprofile_ne hpay0 hpay1

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_selectedEdge_pos_or_zero_outsideCurrent_nonexhaustion_incrementedWeightPayment_pointwise
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hm01 : m0 ≠ m1)
    (hbranch :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        0 < m e0 ∨
          m e0 = 0 ∧
            (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
                (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n v)
                (Function.update m e0 (m e0 + 1)) e0).card <
              (edgeCopySourceSectorSelectedEdgeCopyPairs
                (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n v)
                (Function.update m e0 (m e0 + 1)) e0).card)
    (hpoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          (((1 : ℝ) / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (Function.update (if m = m0 then m1 else m0) e0
                  ((if m = m0 then m1 else m0) e0 + 1)))) /
            384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
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
  have hcell : cell = ({m0, m1} : Finset Profile) := by
    simpa [cell, Ωactive, w] using hcell_pair
  have hactive_of_pair :
      ∀ m ∈ ({m0, m1} : Finset Profile),
        doubledBoxIncrementedFullSourceActive n w e0 m := by
    intro m hm
    have hmcell : m ∈ cell := by
      rw [hcell]
      exact hm
    have hmfilter :
        m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) := by
      simpa [cell] using hmcell
    have hmΩactive : m ∈ Ωactive := (Finset.mem_filter.mp hmfilter).1
    exact (Finset.mem_filter.mp (by simpa [Ωactive] using hmΩactive)).2
  have houtsideCurrent :
      ∀ m ∈ ({m0, m1} : Finset Profile),
        0 <
          (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxInnerPairSource n v w)
            (Function.update m e0 (m e0 + 1)) e0).card := by
    intro m hm
    rcases hbranch m hm with hmpos | hzero
    · exact
        doubledBoxInnerPairSourceSelectedEdgeOutsideCurrent_card_pos_of_strictSectorYPredecessor3_of_selectedEdge_pos
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
          (m := m) hedge hmpos
    · rcases hzero with ⟨hmzero, hstrict⟩
      exact
        doubledBoxInnerPairSourceSelectedEdgeOutsideCurrent_card_pos_of_strictSectorYPredecessor3_of_update_zero_outsideCurrent_card_lt_selectedEdgeCopyPairs_card
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
          (m := m) hedge (by simpa [w] using hactive_of_pair m hm)
          hmzero hstrict
  have hm0_pair : m0 ∈ ({m0, m1} : Finset Profile) := by
    simp
  have hm1_pair : m1 ∈ ({m0, m1} : Finset Profile) := by
    simp
  rcases Finset.card_pos.mp (houtsideCurrent m0 hm0_pair) with ⟨p0, hp0⟩
  rcases Finset.card_pos.mp (houtsideCurrent m1 hm1_pair) with ⟨p1, hp1⟩
  let M0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update m0 e0 (m0 e0 + 1)
  let M1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update m1 e0 (m1 e0 + 1)
  have hprofile0Source :
      Function.update M0 p0.2.1 (M0 p0.2.1 - 1) = m0 := by
    simpa [M0, w] using
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_decrement_increment_profile_eq
        (G := FK.boxGraph 3 (2 * n))
        (A := doubledBoxInnerPairSource n v w)
        (e0 := e0) (m := m0) (p := p0) hp0
  have hprofile1Source :
      Function.update M1 p1.2.1 (M1 p1.2.1 - 1) = m1 := by
    simpa [M1, w] using
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_decrement_increment_profile_eq
        (G := FK.boxGraph 3 (2 * n))
        (A := doubledBoxInnerPairSource n v w)
        (e0 := e0) (m := m1) (p := p1) hp1
  have hprofile_ne :
      Function.update M1 p1.2.1 (M1 p1.2.1 - 1) ≠
        Function.update M0 p0.2.1 (M0 p0.2.1 - 1) := by
    intro hprofile
    apply hm01
    calc
      m0 = Function.update M0 p0.2.1 (M0 p0.2.1 - 1) :=
        hprofile0Source.symm
      _ = Function.update M1 p1.2.1 (M1 p1.2.1 - 1) :=
        hprofile.symm
      _ = m1 := hprofile1Source
  have hpoint0 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m0 ≤
        (((1 : ℝ) / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m1 e0 (m1 e0 + 1)))) /
          384 := by
    simpa [hm01] using hpoint m0 hm0_pair
  have hpoint1 :
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m1 ≤
        (((1 : ℝ) / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (Function.update m0 e0 (m0 e0 + 1)))) /
          384 := by
    simpa [hm01.symm] using hpoint m1 hm1_pair
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_incrementedWeightPayment
      (β := β) hβ (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair
      (p0 := p0) (p1 := p1) hp0 hp1
      (by simpa [M0, M1] using hprofile_ne)
      hpoint0 hpoint1

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_or_exists_zero_outsideCurrent_exhaustion_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_incrementedWeightPayment_pointwise
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
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
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hcell_pair :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = {m0, m1})
    (hm01 : m0 ≠ m1)
    (hpoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          (((1 : ℝ) / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (Function.update (if m = m0 then m1 else m0) e0
                  ((if m = m0 then m1 else m0) e0 + 1)))) /
            384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew ∨
      ∃ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        m e0 = 0 ∧
          (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1)) e0).card =
            (edgeCopySourceSectorSelectedEdgeCopyPairs
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1)) e0).card := by
  classical
  rcases
      doubledBoxOriginToInnerEndpoint_pair_selectedEdge_pos_or_zero_outsideCurrent_nonexhaustion_or_exists_zero_outsideCurrent_exhaustion
        (n := n) (v := v) (e0 := e0) (m0 := m0) (m1 := m1) with
    hbranch | hhard
  · left
    exact
      exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_pair_swappedOutsideCurrentInnerPairSelectedDeletion_selectedEdge_pos_or_zero_outsideCurrent_nonexhaustion_incrementedWeightPayment_pointwise
        (β := β) hβ (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (m0 := m0) (m1 := m1) hedge hcell_pair hm01 hbranch hpoint
  · right
    exact hhard

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_finset
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
    (hcell_rows :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = rows)
    (profileRouteRows :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (witnessRows :
      (m : {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m)))
    (hinj : Function.Injective profileRouteRows)
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m))
          (witnessRows m) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRouteRows m))) \
            witnessRows m) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hpoint :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
            ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun
                  (FK.boxGraph 3 (2 * n))
                  (profileRouteRows ⟨m, hm⟩))) /
              384) :
    ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt
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
  have hcell : cell = rows := by
    simpa [cell, Ωactive, w] using hcell_rows
  let toRows : {m : Profile // m ∈ cell} → {m : Profile // m ∈ rows} :=
    fun m => ⟨m.1, by rw [← hcell]; exact m.2⟩
  let profileRoute : {m : Profile // m ∈ cell} → Profile :=
    fun m => profileRouteRows (toRows m)
  let witness :
      (m : {m : Profile // m ∈ cell}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRoute m)) :=
    fun m => witnessRows (toRows m)
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt]
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a b hroute
    have hrows : toRows a = toRows b := hinj hroute
    have hval : (toRows a).1 = (toRows b).1 :=
      congrArg (fun x : {m : Profile // m ∈ rows} => x.1) hrows
    exact Subtype.ext hval
  · intro m
    simpa [profileRoute, witness] using hleft (toRows m)
  · intro m
    simpa [profileRoute, witness] using hright (toRows m)
  · intro m hm
    have hm_rows : m ∈ rows := by
      rw [← hcell]
      exact hm
    simpa [profileRoute, toRows, w] using hpoint m hm_rows

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_eq_finset
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
    (hcell_rows :
      let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
      let Profile := Edge → ℕ
      let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
      let Ωactive : Finset Profile :=
        Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) = rows)
    (profileRouteRows :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (witnessRows :
      (m : {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m)))
    (hinj : Function.Injective profileRouteRows)
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m))
          (witnessRows m) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRouteRows m))) \
            witnessRows m) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hpoint :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m ≤
            ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun
                  (FK.boxGraph 3 (2 * n))
                  (profileRouteRows ⟨m, hm⟩))) /
              384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
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
  have hcell : cell = rows := by
    simpa [cell, Ωactive, w] using hcell_rows
  let toRows : {m : Profile // m ∈ cell} → {m : Profile // m ∈ rows} :=
    fun m => ⟨m.1, by rw [← hcell]; exact m.2⟩
  let profileRoute : {m : Profile // m ∈ cell} → Profile :=
    fun m => profileRouteRows (toRows m)
  let witness :
      (m : {m : Profile // m ∈ cell}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRoute m)) :=
    fun m => witnessRows (toRows m)
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt]
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a b hroute
    have hrows : toRows a = toRows b := hinj hroute
    have hval : (toRows a).1 = (toRows b).1 :=
      congrArg (fun x : {m : Profile // m ∈ rows} => x.1) hrows
    exact Subtype.ext hval
  · intro m
    simpa [profileRoute, witness, w] using hleft (toRows m)
  · intro m
    simpa [profileRoute, witness, w] using hright (toRows m)
  · intro m hm
    have hm_rows : m ∈ rows := by
      rw [← hcell]
      exact hm
    simpa [profileRoute, toRows, w] using hpoint m hm_rows

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt_of_cell_subset_finset
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
    (profileRouteRows :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (witnessRows :
      (m : {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m)))
    (hinj : Function.Injective profileRouteRows)
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m))
          (witnessRows m) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRouteRows m))) \
            witnessRows m) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hpoint :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
            ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun
                  (FK.boxGraph 3 (2 * n))
                  (profileRouteRows ⟨m, hm⟩))) /
              384) :
    ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt
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
  have hsubset : ∀ m : Profile, m ∈ cell → m ∈ rows := by
    simpa [cell, Ωactive, w] using hcell_subset
  let toRows : {m : Profile // m ∈ cell} → {m : Profile // m ∈ rows} :=
    fun m => ⟨m.1, hsubset m.1 m.2⟩
  let profileRoute : {m : Profile // m ∈ cell} → Profile :=
    fun m => profileRouteRows (toRows m)
  let witness :
      (m : {m : Profile // m ∈ cell}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRoute m)) :=
    fun m => witnessRows (toRows m)
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt]
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a b hroute
    have hrows : toRows a = toRows b := hinj hroute
    have hval : (toRows a).1 = (toRows b).1 :=
      congrArg (fun x : {m : Profile // m ∈ rows} => x.1) hrows
    exact Subtype.ext hval
  · intro m
    simpa [profileRoute, witness] using hleft (toRows m)
  · intro m
    simpa [profileRoute, witness] using hright (toRows m)
  · intro m hm
    have hm_rows : m ∈ rows := hsubset m hm
    simpa [profileRoute, toRows, w] using hpoint m hm_rows

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_subset_finset
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
    (profileRouteRows :
      {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows} →
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (witnessRows :
      (m : {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ // m ∈ rows}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m)))
    (hinj : Function.Injective profileRouteRows)
    (hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m))
          (witnessRows m) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRouteRows m))) \
            witnessRows m) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hpoint :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m ≤
            ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun
                  (FK.boxGraph 3 (2 * n))
                  (profileRouteRows ⟨m, hm⟩))) /
              384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
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
  have hsubset : ∀ m : Profile, m ∈ cell → m ∈ rows := by
    simpa [cell, Ωactive, w] using hcell_subset
  let toRows : {m : Profile // m ∈ cell} → {m : Profile // m ∈ rows} :=
    fun m => ⟨m.1, hsubset m.1 m.2⟩
  let profileRoute : {m : Profile // m ∈ cell} → Profile :=
    fun m => profileRouteRows (toRows m)
  let witness :
      (m : {m : Profile // m ∈ cell}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRoute m)) :=
    fun m => witnessRows (toRows m)
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt]
  refine ⟨profileRoute, witness, ?_, ?_, ?_, ?_⟩
  · intro a b hroute
    have hrows : toRows a = toRows b := hinj hroute
    have hval : (toRows a).1 = (toRows b).1 :=
      congrArg (fun x : {m : Profile // m ∈ rows} => x.1) hrows
    exact Subtype.ext hval
  · intro m
    simpa [profileRoute, witness, w] using hleft (toRows m)
  · intro m
    simpa [profileRoute, witness, w] using hright (toRows m)
  · intro m hm
    have hm_rows : m ∈ rows := hsubset m hm
    simpa [profileRoute, toRows, w] using hpoint m hm_rows

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt_of_cell_subset_pair_pointwise
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
    (profile0 profile1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hprofile_ne : profile0 ≠ profile1)
    (witness0 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile0))
    (witness1 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile1))
    (hleft0 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        witness0 =
        doubledBoxOriginToInnerEndpointSource n v)
    (hleft1 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile1)
        witness1 =
        doubledBoxOriginToInnerEndpointSource n v)
    (hright0 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) profile0)) \
          witness0) =
        (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hright1 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile1)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) profile1)) \
          witness1) =
        (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hpoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then profile0 else profile1))) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let Profile := ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ
  let rows : Finset Profile := {m0, m1}
  let profileRouteRows : {m : Profile // m ∈ rows} → Profile :=
    fun m => if m.1 = m0 then profile0 else profile1
  let witnessRows :
      (m : {m : Profile // m ∈ rows}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m)) :=
    fun m =>
      if hm0 : m.1 = m0 then
        fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile0) (m' := profileRouteRows m)
          (by simp [profileRouteRows, hm0]) witness0
      else
        fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile1) (m' := profileRouteRows m)
          (by simp [profileRouteRows, hm0]) witness1
  have hinj : Function.Injective profileRouteRows := by
    intro a b hroute
    apply Subtype.ext
    by_cases ha0 : a.1 = m0
    · by_cases hb0 : b.1 = m0
      · exact ha0.trans hb0.symm
      · have hpa : profileRouteRows a = profile0 := by
          dsimp [profileRouteRows]
          exact if_pos ha0
        have hpb : profileRouteRows b = profile1 := by
          dsimp [profileRouteRows]
          exact if_neg hb0
        have hp01 : profile0 = profile1 := by
          calc
            profile0 = profileRouteRows a := hpa.symm
            _ = profileRouteRows b := hroute
            _ = profile1 := hpb
        exact False.elim (hprofile_ne hp01)
    · by_cases hb0 : b.1 = m0
      · have hpa : profileRouteRows a = profile1 := by
          dsimp [profileRouteRows]
          exact if_neg ha0
        have hpb : profileRouteRows b = profile0 := by
          dsimp [profileRouteRows]
          exact if_pos hb0
        have hp10 : profile1 = profile0 := by
          calc
            profile1 = profileRouteRows a := hpa.symm
            _ = profileRouteRows b := hroute
            _ = profile0 := hpb
        exact False.elim (hprofile_ne hp10.symm)
      · have ha_or : a.1 = m0 ∨ a.1 = m1 := by
          have ha_pair :
              a.1 ∈ ({m0, m1} : Finset Profile) := by
            change a.1 ∈ rows
            exact a.2
          rcases Finset.mem_insert.mp ha_pair with ha | ha
          · exact Or.inl ha
          · exact Or.inr (by simpa using ha)
        have hb_or : b.1 = m0 ∨ b.1 = m1 := by
          have hb_pair :
              b.1 ∈ ({m0, m1} : Finset Profile) := by
            change b.1 ∈ rows
            exact b.2
          rcases Finset.mem_insert.mp hb_pair with hb | hb
          · exact Or.inl hb
          · exact Or.inr (by simpa using hb)
        exact (ha_or.resolve_left ha0).trans
          (hb_or.resolve_left hb0).symm
  have hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m))
          (witnessRows m) =
          doubledBoxOriginToInnerEndpointSource n v := by
    intro m
    by_cases hm0 : m.1 = m0
    · dsimp only [witnessRows]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile0) (m' := profileRouteRows m)
          (by simp [profileRouteRows, hm0]) witness0).trans hleft0
    · dsimp only [witnessRows]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile1) (m' := profileRouteRows m)
          (by simp [profileRouteRows, hm0]) witness1).trans hleft1
  have hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRouteRows m))) \
            witnessRows m) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
    intro m
    by_cases hm0 : m.1 = m0
    · dsimp only [witnessRows]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile0) (m' := profileRouteRows m)
          (by simp [profileRouteRows, hm0]) witness0).trans hright0
    · dsimp only [witnessRows]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile1) (m' := profileRouteRows m)
          (by simp [profileRouteRows, hm0]) witness1).trans hright1
  have hpointRows :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
            ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun
                  (FK.boxGraph 3 (2 * n))
                  (profileRouteRows ⟨m, hm⟩))) /
              384 := by
    intro m hm
    simpa [rows, profileRouteRows] using hpoint m (by simpa [rows] using hm)
  exact
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt_of_cell_subset_finset
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (rows := rows) (by simpa [rows] using hcell_subset)
      profileRouteRows witnessRows hinj hleft hright hpointRows

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_subset_pair_pointwise
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
    (profile0 profile1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hprofile_ne : profile0 ≠ profile1)
    (witness0 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile0))
    (witness1 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile1))
    (hleft0 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        witness0 =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hleft1 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile1)
        witness1 =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hright0 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile0)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) profile0)) \
          witness0) =
        doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hright1 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile1)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) profile1)) \
          witness1) =
        doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hpoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then profile0 else profile1))) /
            384) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let Profile := ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ
  let rows : Finset Profile := {m0, m1}
  let profileRouteRows : {m : Profile // m ∈ rows} → Profile :=
    fun m => if m.1 = m0 then profile0 else profile1
  let witnessRows :
      (m : {m : Profile // m ∈ rows}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m)) :=
    fun m =>
      if hm0 : m.1 = m0 then
        fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile0) (m' := profileRouteRows m)
          (by simp [profileRouteRows, hm0]) witness0
      else
        fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile1) (m' := profileRouteRows m)
          (by simp [profileRouteRows, hm0]) witness1
  have hinj : Function.Injective profileRouteRows := by
    intro a b hroute
    apply Subtype.ext
    by_cases ha0 : a.1 = m0
    · by_cases hb0 : b.1 = m0
      · exact ha0.trans hb0.symm
      · have hpa : profileRouteRows a = profile0 := by
          dsimp [profileRouteRows]
          exact if_pos ha0
        have hpb : profileRouteRows b = profile1 := by
          dsimp [profileRouteRows]
          exact if_neg hb0
        have hp01 : profile0 = profile1 := by
          calc
            profile0 = profileRouteRows a := hpa.symm
            _ = profileRouteRows b := hroute
            _ = profile1 := hpb
        exact False.elim (hprofile_ne hp01)
    · by_cases hb0 : b.1 = m0
      · have hpa : profileRouteRows a = profile1 := by
          dsimp [profileRouteRows]
          exact if_neg ha0
        have hpb : profileRouteRows b = profile0 := by
          dsimp [profileRouteRows]
          exact if_pos hb0
        have hp10 : profile1 = profile0 := by
          calc
            profile1 = profileRouteRows a := hpa.symm
            _ = profileRouteRows b := hroute
            _ = profile0 := hpb
        exact False.elim (hprofile_ne hp10.symm)
      · have ha_or : a.1 = m0 ∨ a.1 = m1 := by
          have ha_pair :
              a.1 ∈ ({m0, m1} : Finset Profile) := by
            change a.1 ∈ rows
            exact a.2
          rcases Finset.mem_insert.mp ha_pair with ha | ha
          · exact Or.inl ha
          · exact Or.inr (by simpa using ha)
        have hb_or : b.1 = m0 ∨ b.1 = m1 := by
          have hb_pair :
              b.1 ∈ ({m0, m1} : Finset Profile) := by
            change b.1 ∈ rows
            exact b.2
          rcases Finset.mem_insert.mp hb_pair with hb | hb
          · exact Or.inl hb
          · exact Or.inr (by simpa using hb)
        exact (ha_or.resolve_left ha0).trans
          (hb_or.resolve_left hb0).symm
  have hleft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m))
          (witnessRows m) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
    intro m
    by_cases hm0 : m.1 = m0
    · dsimp only [witnessRows]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile0) (m' := profileRouteRows m)
          (by simp [profileRouteRows, hm0]) witness0).trans hleft0
    · dsimp only [witnessRows]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile1) (m' := profileRouteRows m)
          (by simp [profileRouteRows, hm0]) witness1).trans hleft1
  have hright :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (profileRouteRows m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (profileRouteRows m))) \
            witnessRows m) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
    intro m
    by_cases hm0 : m.1 = m0
    · dsimp only [witnessRows]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile0) (m' := profileRouteRows m)
          (by simp [profileRouteRows, hm0]) witness0).trans hright0
    · dsimp only [witnessRows]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := profile1) (m' := profileRouteRows m)
          (by simp [profileRouteRows, hm0]) witness1).trans hright1
  have hpointRows :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m ≤
            ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun
                  (FK.boxGraph 3 (2 * n))
                  (profileRouteRows ⟨m, hm⟩))) /
              384 := by
    intro m hm
    simpa [rows, profileRouteRows] using hpoint m (by simpa [rows] using hm)
  exact
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_subset_finset
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (rows := rows) (by simpa [rows] using hcell_subset)
      profileRouteRows witnessRows hinj hleft hright hpointRows

end Exact3D
end StatMech
