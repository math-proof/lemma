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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part111
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_subset_pair_pointwise
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
    (emptyProfile0 emptyProfile1 :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hemptyProfile_ne : emptyProfile0 ≠ emptyProfile1)
    (emptyWitness0 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy
          (FK.boxGraph 3 (2 * n)) emptyProfile0))
    (emptyWitness1 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy
          (FK.boxGraph 3 (2 * n)) emptyProfile1))
    (hemptyLeft0 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (FK.boxGraph 3 (2 * n)) emptyProfile0)
        emptyWitness0 =
        doubledBoxOriginToInnerEndpointSource n v)
    (hemptyLeft1 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (FK.boxGraph 3 (2 * n)) emptyProfile1)
        emptyWitness1 =
        doubledBoxOriginToInnerEndpointSource n v)
    (hemptyRight0 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (FK.boxGraph 3 (2 * n)) emptyProfile0)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) emptyProfile0)) \
          emptyWitness0) =
        (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hemptyRight1 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (FK.boxGraph 3 (2 * n)) emptyProfile1)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) emptyProfile1)) \
          emptyWitness1) =
        (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hemptyPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then emptyProfile0 else emptyProfile1))) /
            384)
    (innerProfile0 innerProfile1 :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hinnerProfile_ne : innerProfile0 ≠ innerProfile1)
    (innerWitness0 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy
          (FK.boxGraph 3 (2 * n)) innerProfile0))
    (innerWitness1 :
      Finset
        (Sharpness.FluxEdgeCopy.Copy
          (FK.boxGraph 3 (2 * n)) innerProfile1))
    (hinnerLeft0 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (FK.boxGraph 3 (2 * n)) innerProfile0)
        innerWitness0 =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hinnerLeft1 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (FK.boxGraph 3 (2 * n)) innerProfile1)
        innerWitness1 =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hinnerRight0 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (FK.boxGraph 3 (2 * n)) innerProfile0)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) innerProfile0)) \
          innerWitness0) =
        doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hinnerRight1 :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (FK.boxGraph 3 (2 * n)) innerProfile1)
        ((Finset.univ :
            Finset
              (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n)) innerProfile1)) \
          innerWitness1) =
        doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hinnerPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then innerProfile0 else innerProfile1))) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let Profile := ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ
  let rows : Finset Profile := {m0, m1}
  have pairRoute_injective :
      ∀ {profile0 profile1 : Profile},
        profile0 ≠ profile1 →
          Function.Injective
            (fun m : {m : Profile // m ∈ rows} =>
              if m.1 = m0 then profile0 else profile1) := by
    intro profile0 profile1 hprofile_ne a b hroute
    apply Subtype.ext
    by_cases ha0 : a.1 = m0
    · by_cases hb0 : b.1 = m0
      · exact ha0.trans hb0.symm
      · have hp01 : profile0 = profile1 := by
          calc
            profile0 =
                (if a.1 = m0 then profile0 else profile1) := (if_pos ha0).symm
            _ = (if b.1 = m0 then profile0 else profile1) := hroute
            _ = profile1 := if_neg hb0
        exact False.elim (hprofile_ne hp01)
    · by_cases hb0 : b.1 = m0
      · have hp10 : profile1 = profile0 := by
          calc
            profile1 =
                (if a.1 = m0 then profile0 else profile1) := (if_neg ha0).symm
            _ = (if b.1 = m0 then profile0 else profile1) := hroute
            _ = profile0 := if_pos hb0
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
  let emptyProfileRouteRows : {m : Profile // m ∈ rows} → Profile :=
    fun m => if m.1 = m0 then emptyProfile0 else emptyProfile1
  let emptyWitnessRows :
      (m : {m : Profile // m ∈ rows}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (emptyProfileRouteRows m)) :=
    fun m =>
      if hm0 : m.1 = m0 then
        fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := emptyProfile0) (m' := emptyProfileRouteRows m)
          (by simp [emptyProfileRouteRows, hm0]) emptyWitness0
      else
        fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := emptyProfile1) (m' := emptyProfileRouteRows m)
          (by simp [emptyProfileRouteRows, hm0]) emptyWitness1
  have hemptyInj : Function.Injective emptyProfileRouteRows := by
    exact pairRoute_injective hemptyProfile_ne
  have hemptyLeft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (emptyProfileRouteRows m))
          (emptyWitnessRows m) =
          doubledBoxOriginToInnerEndpointSource n v := by
    intro m
    by_cases hm0 : m.1 = m0
    · dsimp only [emptyWitnessRows]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := emptyProfile0) (m' := emptyProfileRouteRows m)
          (by simp [emptyProfileRouteRows, hm0]) emptyWitness0).trans
            hemptyLeft0
    · dsimp only [emptyWitnessRows]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := emptyProfile1) (m' := emptyProfileRouteRows m)
          (by simp [emptyProfileRouteRows, hm0]) emptyWitness1).trans
            hemptyLeft1
  have hemptyRight :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (emptyProfileRouteRows m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (emptyProfileRouteRows m))) \
            emptyWitnessRows m) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
    intro m
    by_cases hm0 : m.1 = m0
    · dsimp only [emptyWitnessRows]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := emptyProfile0) (m' := emptyProfileRouteRows m)
          (by simp [emptyProfileRouteRows, hm0]) emptyWitness0).trans
            hemptyRight0
    · dsimp only [emptyWitnessRows]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := emptyProfile1) (m' := emptyProfileRouteRows m)
          (by simp [emptyProfileRouteRows, hm0]) emptyWitness1).trans
            hemptyRight1
  have hemptyPointRows :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
            ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun
                  (FK.boxGraph 3 (2 * n))
                  (emptyProfileRouteRows ⟨m, hm⟩))) /
              384 := by
    intro m hm
    simpa [rows, emptyProfileRouteRows] using
      hemptyPoint m (by simpa [rows] using hm)
  let innerProfileRouteRows : {m : Profile // m ∈ rows} → Profile :=
    fun m => if m.1 = m0 then innerProfile0 else innerProfile1
  let innerWitnessRows :
      (m : {m : Profile // m ∈ rows}) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (innerProfileRouteRows m)) :=
    fun m =>
      if hm0 : m.1 = m0 then
        fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := innerProfile0) (m' := innerProfileRouteRows m)
          (by simp [innerProfileRouteRows, hm0]) innerWitness0
      else
        fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := innerProfile1) (m' := innerProfileRouteRows m)
          (by simp [innerProfileRouteRows, hm0]) innerWitness1
  have hinnerInj : Function.Injective innerProfileRouteRows := by
    exact pairRoute_injective hinnerProfile_ne
  have hinnerLeft :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (innerProfileRouteRows m))
          (innerWitnessRows m) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
    intro m
    by_cases hm0 : m.1 = m0
    · dsimp only [innerWitnessRows]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := innerProfile0) (m' := innerProfileRouteRows m)
          (by simp [innerProfileRouteRows, hm0]) innerWitness0).trans
            hinnerLeft0
    · dsimp only [innerWitnessRows]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := innerProfile1) (m' := innerProfileRouteRows m)
          (by simp [innerProfileRouteRows, hm0]) innerWitness1).trans
            hinnerLeft1
  have hinnerRight :
      ∀ m,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (innerProfileRouteRows m))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (innerProfileRouteRows m))) \
            innerWitnessRows m) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
    intro m
    by_cases hm0 : m.1 = m0
    · dsimp only [innerWitnessRows]
      rw [dif_pos hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := innerProfile0) (m' := innerProfileRouteRows m)
          (by simp [innerProfileRouteRows, hm0]) innerWitness0).trans
            hinnerRight0
    · dsimp only [innerWitnessRows]
      rw [dif_neg hm0]
      exact
        (randomCurrent_sources_univ_sdiff_fluxEdgeCopyFinsetCast
          (G := FK.boxGraph 3 (2 * n))
          (m := innerProfile1) (m' := innerProfileRouteRows m)
          (by simp [innerProfileRouteRows, hm0]) innerWitness1).trans
            hinnerRight1
  have hinnerPointRows :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m ≤
            ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun
                  (FK.boxGraph 3 (2 * n))
                  (innerProfileRouteRows ⟨m, hm⟩))) /
              384 := by
    intro m hm
    simpa [rows, innerProfileRouteRows] using
      hinnerPoint m (by simpa [rows] using hm)
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt]
  refine ⟨rows, ?_, ?_, ?_⟩
  · simpa [rows] using hcell_subset
  · exact
      ⟨emptyProfileRouteRows, emptyWitnessRows, hemptyInj, hemptyLeft,
        hemptyRight, hemptyPointRows⟩
  · exact
      ⟨innerProfileRouteRows, innerWitnessRows, hinnerInj, hinnerLeft,
        hinnerRight, hinnerPointRows⟩

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_inCurrent_card_pos_pointwise
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
    (hemptyPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384)
    (hinnerPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
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
  have hm0_pair : m0 ∈ ({m0, m1} : Finset Profile) := by
    simp
  have hm1_pair : m1 ∈ ({m0, m1} : Finset Profile) := by
    simp
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
  have hcell_subset :
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
          m ∈ ({m0, m1} : Finset Profile) := by
    dsimp only
    intro m hm
    have hm_cell : m ∈ cell := by
      simpa [cell, Ωactive, w] using hm
    rw [hcell] at hm_cell
    simpa using hm_cell
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_switched_emptySourceEquations_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m1) hedge (by simpa [w] using hm1_active) hm1_owner with
    ⟨emptyProfile1, emptyWitness1, hemptyProfile1, hemptyLeft1,
      hemptyRight1⟩
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_switched_emptySourceEquations_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m0) hedge (by simpa [w] using hm0_active) hm0_owner with
    ⟨emptyProfile0, emptyWitness0, hemptyProfile0, hemptyLeft0,
      hemptyRight0⟩
  have hemptyProfile_ne : emptyProfile1 ≠ emptyProfile0 := by
    intro hprofile
    apply hm01
    calc
      m0 = emptyProfile0 := hemptyProfile0.symm
      _ = emptyProfile1 := hprofile.symm
      _ = m1 := hemptyProfile1
  rcases Finset.card_pos.mp (hinCurrent m0 hm0_pair) with
    ⟨p0, hp0⟩
  rcases Finset.card_pos.mp (hinCurrent m1 hm1_pair) with
    ⟨p1, hp1⟩
  rcases
      doubledBoxIncrementedFullSourceActive_inCurrentSelectedDeletion_switched_innerPairSourceEquations_profile_eq_row_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m1)
        hedge (by simpa [w] using hm1_active) (p := p1) hp1 with
    ⟨innerProfile1, innerWitness1, hinnerProfile1, hinnerLeft1,
      hinnerRight1⟩
  rcases
      doubledBoxIncrementedFullSourceActive_inCurrentSelectedDeletion_switched_innerPairSourceEquations_profile_eq_row_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m0)
        hedge (by simpa [w] using hm0_active) (p := p0) hp0 with
    ⟨innerProfile0, innerWitness0, hinnerProfile0, hinnerLeft0,
      hinnerRight0⟩
  have hinnerProfile_ne : innerProfile1 ≠ innerProfile0 := by
    intro hprofile
    apply hm01
    calc
      m0 = innerProfile0 := hinnerProfile0.symm
      _ = innerProfile1 := hprofile.symm
      _ = m1 := hinnerProfile1
  exact
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_subset_pair_pointwise
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hcell_subset
      emptyProfile1 emptyProfile0 hemptyProfile_ne
      emptyWitness1 emptyWitness0
      hemptyLeft1 hemptyLeft0 hemptyRight1 hemptyRight0
      (by
        intro m hm
        simpa [hemptyProfile1, hemptyProfile0] using hemptyPoint m hm)
      innerProfile1 innerProfile0 hinnerProfile_ne
      innerWitness1 innerWitness0
      hinnerLeft1 hinnerLeft0 hinnerRight1 hinnerRight0
      (by
        intro m hm
        simpa [hinnerProfile1, hinnerProfile0] using hinnerPoint m hm)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_selectedEdge_pos_pointwise
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
    (hmpos :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        0 < m e0)
    (hemptyPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384)
    (hinnerPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
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
  have hinCurrent :
      ∀ m ∈ ({m0, m1} : Finset Profile),
        0 <
          (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card := by
    intro m hm
    exact
      doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairsInCurrent_card_pos_of_strictSectorYPredecessor3_of_selectedEdge_pos
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
        hedge (by simpa [w] using hactive_of_pair m hm) (hmpos m hm)
  exact
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_inCurrent_card_pos_pointwise
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01 hinCurrent
      hemptyPoint hinnerPoint

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_selectedEdge_pos_or_zero_containing_incrementInserted_card_pos_pointwise
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
    (hemptyPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384)
    (hinnerPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
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
  have hinCurrent :
      ∀ m ∈ ({m0, m1} : Finset Profile),
        0 <
          (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card := by
    intro m hm
    rcases hbranch m hm with hmpos | hzero
    · exact
        doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairsInCurrent_card_pos_of_strictSectorYPredecessor3_of_selectedEdge_pos
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
          hedge (by simpa [w] using hactive_of_pair m hm) hmpos
    · rcases hzero with ⟨hmzero, hcontaining⟩
      have hcard :=
        edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_card_eq_containing_incrementInserted_card_of_update_zero
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v) m e0 hmzero
      rw [hcard]
      exact hcontaining
  exact
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_inCurrent_card_pos_pointwise
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01 hinCurrent
      hemptyPoint hinnerPoint

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_selectedEdge_pos_or_zero_outsideCurrent_nonexhaustion_pointwise
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
    (hemptyPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384)
    (hinnerPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
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
  have hinCurrent :
      ∀ m ∈ ({m0, m1} : Finset Profile),
        0 <
          (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card := by
    intro m hm
    rcases hbranch m hm with hmpos | hzero
    · exact
        doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairsInCurrent_card_pos_of_strictSectorYPredecessor3_of_selectedEdge_pos
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
          hedge (by simpa [w] using hactive_of_pair m hm) hmpos
    · rcases hzero with ⟨_hmzero, hstrict⟩
      exact
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_card_lt_total_iff_inCurrent_card_pos
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).mp hstrict
  exact
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_inCurrent_card_pos_pointwise
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01 hinCurrent
      hemptyPoint hinnerPoint

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_zero_outsideCurrent_exhaustion_of_cell_eq_pair_swappedSelectedDeletion_pointwise
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
    (hemptyPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384)
    (hinnerPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
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
      exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_selectedEdge_pos_or_zero_outsideCurrent_nonexhaustion_pointwise
        (β := β) (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (m0 := m0) (m1 := m1) hedge hcell_pair hm01 hbranch
        hemptyPoint hinnerPoint
  · right
    exact hhard

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_pointwise
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
            ((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n
                  (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                m).Nonempty ∨
              ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                  m).Nonempty) ∧
                (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
                  (FK.boxGraph 3 (2 * n))
                  (doubledBoxOriginToInnerEndpointSource n v)
                  (Function.update m e0 (m e0 + 1)) e0).Nonempty)))
    (hemptyPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384)
    (hinnerPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
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
    ⟨_edge, _hedgeData, hov, how, hvw⟩
  have hinCurrent :
      ∀ m ∈ ({m0, m1} : Finset Profile),
        0 <
          (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card := by
    intro m hm
    rcases hbranch m hm with hmpos | hzero
    · exact
        doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairsInCurrent_card_pos_of_strictSectorYPredecessor3_of_selectedEdge_pos
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
          hedge (by simpa [w] using hactive_of_pair m hm) hmpos
    · rcases hzero with ⟨hmzero, hsourceOrResidual⟩
      rcases hsourceOrResidual with hsource | hresidual
      · have hin :
            (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1)) e0).Nonempty :=
          doubledBoxOriginToInnerEndpoint_selectedEdgeCopyPairsInCurrent_nonempty_of_predecessorSourceSector_nonempty_update_zero
            (n := n) (v := v) (w := w) (m := m) (e0 := e0) hmzero
            (by simpa [w] using hedge) hov how hvw hsource
        exact Finset.Nonempty.card_pos hin
      · exact Finset.Nonempty.card_pos hresidual.2
  exact
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_inCurrent_card_pos_pointwise
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01 hinCurrent
      hemptyPoint hinnerPoint

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_selectedCopyPointwise
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
            ((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n
                  (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                m).Nonempty ∨
              ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                  m).Nonempty) ∧
                (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
                  (FK.boxGraph 3 (2 * n))
                  (doubledBoxOriginToInnerEndpointSource n v)
                  (Function.update m e0 (m e0 + 1)) e0).Nonempty)))
    (hemptySelectedPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          (Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0)) /
            6) /
            384)
    (hinnerSelectedPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
          (Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0)) /
            6) /
            384) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  have hemptyPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            w e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384 := by
    intro m hm
    exact
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_le_beta_div_six_weight_div_384_of_totalPairCardEmpty_le_weight_div_six_div_384
        (β := β) (W :=
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (if m = m0 then m1 else m0)))
        hβ (n := n) (v := v) (w := w) e0 m
        (by simpa [w] using hemptySelectedPoint m hm)
  have hinnerPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v w e0 m ≤
          ((β / 6) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0))) /
            384 := by
    intro m hm
    exact
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_le_beta_div_six_weight_div_384_of_totalPairCardInner_le_weight_div_six_div_384
        (β := β) (W :=
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (if m = m0 then m1 else m0)))
        hβ (n := n) (v := v) (w := w) e0 m
        (by simpa [w] using hinnerSelectedPoint m hm)
  exact
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_pointwise
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01 hbranch
      (by simpa [w] using hemptyPoint)
      (by simpa [w] using hinnerPoint)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_splitSelectedCopyPointwise
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
            ((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n
                  (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                m).Nonempty ∨
              ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                  m).Nonempty) ∧
                (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
                  (FK.boxGraph 3 (2 * n))
                  (doubledBoxOriginToInnerEndpointSource n v)
                  (Function.update m e0 (m e0 + 1)) e0).Nonempty)))
    (hemptyInSelectedPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
          (Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0)) /
            6) /
            768)
    (hemptyOutSelectedPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
          (Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0)) /
            6) /
            768)
    (hinnerInSelectedPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
          (Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0)) /
            6) /
            768)
    (hinnerOutSelectedPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 m ≤
          (Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0)) /
            6) /
            768) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  have hemptySelectedPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n v
            w e0 m ≤
          (Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0)) /
            6) /
            384 := by
    intro m hm
    exact
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_le_weight_div_six_div_384_of_inCurrent_outsideCurrent_le_weight_div_six_div_768
        (β := β)
        (W :=
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (if m = m0 then m1 else m0)))
        (n := n) (v := v) (w := w) (e0 := e0) (m := m)
        (by simpa [w] using hemptyInSelectedPoint m hm)
        (by simpa [w] using hemptyOutSelectedPoint m hm)
  have hinnerSelectedPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
            β n v w e0 m ≤
          (Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                (if m = m0 then m1 else m0)) /
            6) /
            384 := by
    intro m hm
    exact
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_le_weight_div_six_div_384_of_inCurrent_outsideCurrent_le_weight_div_six_div_768
        (β := β)
        (W :=
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (if m = m0 then m1 else m0)))
        (n := n) (v := v) (w := w) (e0 := e0) (m := m)
        (by simpa [w] using hinnerInSelectedPoint m hm)
        (by simpa [w] using hinnerOutSelectedPoint m hm)
  exact
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_selectedCopyPointwise
      (β := β) hβ (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01 hbranch
      (by simpa [w] using hemptySelectedPoint)
      (by simpa [w] using hinnerSelectedPoint)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_betaWeightedSplitSelectedCopyPointwise
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
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
            ((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n
                  (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                m).Nonempty ∨
              ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                  m).Nonempty) ∧
                (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
                  (FK.boxGraph 3 (2 * n))
                  (doubledBoxOriginToInnerEndpointSource n v)
                  (Function.update m e0 (m e0 + 1)) e0).Nonempty)))
    (hemptyInSelectedPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        β *
            doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768)
    (hemptyOutSelectedPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        β *
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768)
    (hinnerInSelectedPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        β *
            doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768)
    (hinnerOutSelectedPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        β *
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  exact
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_splitSelectedCopyPointwise
      (β := β) hβpos.le (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01 hbranch
      (by
        intro m hm
        exact
          selectedCopyBranch_le_weight_div_six_div_768_of_beta_mul_le_beta_div_six_weight_div_768
            (β := β)
            (W :=
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0)))
            (X :=
              doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
                β n v w e0 m)
            hβpos
            (by simpa [w] using hemptyInSelectedPoint m hm))
      (by
        intro m hm
        exact
          selectedCopyBranch_le_weight_div_six_div_768_of_beta_mul_le_beta_div_six_weight_div_768
            (β := β)
            (W :=
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0)))
            (X :=
              doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
                β n v w e0 m)
            hβpos
            (by simpa [w] using hemptyOutSelectedPoint m hm))
      (by
        intro m hm
        exact
          selectedCopyBranch_le_weight_div_six_div_768_of_beta_mul_le_beta_div_six_weight_div_768
            (β := β)
            (W :=
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0)))
            (X :=
              doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
                β n v w e0 m)
            hβpos
            (by simpa [w] using hinnerInSelectedPoint m hm))
      (by
        intro m hm
        exact
          selectedCopyBranch_le_weight_div_six_div_768_of_beta_mul_le_beta_div_six_weight_div_768
            (β := β)
            (W :=
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0)))
            (X :=
              doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
                β n v w e0 m)
            hβpos
            (by simpa [w] using hinnerOutSelectedPoint m hm))

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_residualMomentDiv768Pointwise
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
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
            ((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n
                  (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                m).Nonempty ∨
              ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                  (doubledBoxOriginToInnerEndpointSource n
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                  m).Nonempty) ∧
                (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
                  (FK.boxGraph 3 (2 * n))
                  (doubledBoxOriginToInnerEndpointSource n v)
                  (Function.update m e0 (m e0 + 1)) e0).Nonempty)))
    (hemptyResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768)
    (hinnerResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  exact
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_betaWeightedSplitSelectedCopyPointwise
      (β := β) hβpos (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01 hbranch
      (by
        intro m hm
        exact
          beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentEmptyBranchSummand_le_beta_div_six_weight_div_768
            (β := β)
            (W :=
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0)))
            hβpos.le (n := n) (v := v) (w := w) e0 m
            (by simpa [w] using hemptyResidualPoint m hm))
      (by
        intro m hm
        exact
          beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentEmptyBranchSummand_le_beta_div_six_weight_div_768
            (β := β)
            (W :=
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0)))
            hβpos.le (n := n) (v := v) (w := w) e0 m
            (by simpa [w] using hemptyResidualPoint m hm))
      (by
        intro m hm
        exact
          beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentInnerPairBranchSummand_le_beta_div_six_weight_div_768
            (β := β)
            (W :=
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0)))
            hβpos.le (n := n) (v := v) (w := w) e0 m
            (by simpa [w] using hinnerResidualPoint m hm))
      (by
        intro m hm
        exact
          beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_le_beta_div_six_weight_div_768_of_switchedSourceSectorResidualMomentInnerPairBranchSummand_le_beta_div_six_weight_div_768
            (β := β)
            (W :=
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0)))
            hβpos.le (n := n) (v := v) (w := w) e0 m
            (by simpa [w] using hinnerResidualPoint m hm))

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_zero_noPredecessor_outsideCurrent_exhaustion_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
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
    (hemptyResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768)
    (hinnerResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew ∨
      ∃ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        m e0 = 0 ∧
          (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              m).Nonempty) ∧
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
      doubledBoxOriginToInnerEndpoint_pair_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_or_exists_zero_noPredecessor_outsideCurrent_exhaustion
        (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) (m0 := m0) (m1 := m1) with
    hbranch | hhard
  · left
    exact
      exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_cell_eq_pair_swappedSelectedDeletion_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_residualMomentDiv768Pointwise
        (β := β) hβpos (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (m0 := m0) (m1 := m1) hedge hcell_pair hm01 hbranch
        hemptyResidualPoint hinnerResidualPoint
  · right
    exact hhard

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_zero_noPredecessor_noInCurrent_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
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
    (hemptyResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768)
    (hinnerResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew ∨
      ∃ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        m e0 = 0 ∧
          (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              m).Nonempty) ∧
          ¬ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1)) e0).Nonempty := by
  classical
  rcases
      exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_zero_noPredecessor_outsideCurrent_exhaustion_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
        (β := β) hβpos (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (m0 := m0) (m1 := m1) hedge hcell_pair hm01
        hemptyResidualPoint hinnerResidualPoint with
    hcover | hhard
  · exact Or.inl hcover
  · right
    rcases hhard with ⟨m, hm, hrow⟩
    refine ⟨m, hm, ?_⟩
    exact
      (doubledBoxOriginToInnerEndpoint_zero_noPredecessor_outsideCurrent_exhaustion_iff_zero_noPredecessor_noInCurrent
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)).mp
        hrow

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_zero_noPredecessor_noContaining_incrementInserted_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
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
    (hemptyResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768)
    (hinnerResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew ∨
      ∃ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        m e0 = 0 ∧
          (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              m).Nonempty) ∧
          ¬ (edgeCopySourceSectorContainingCopy
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1))
              (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).Nonempty := by
  classical
  rcases
      exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_zero_noPredecessor_noInCurrent_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
        (β := β) hβpos (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (m0 := m0) (m1 := m1) hedge hcell_pair hm01
        hemptyResidualPoint hinnerResidualPoint with
    hcover | hhard
  · exact Or.inl hcover
  · right
    rcases hhard with ⟨m, hm, hrow⟩
    refine ⟨m, hm, ?_⟩
    exact
      (doubledBoxOriginToInnerEndpoint_zero_noPredecessor_noInCurrent_iff_zero_noPredecessor_noContaining_incrementInserted
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)).mp
        hrow

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_active_zero_noPredecessor_allSwitchedRowsAvoidIncrementInserted_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
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
    (hemptyResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768)
    (hinnerResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew ∨
      ∃ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ∧
          m e0 = 0 ∧
          (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              m).Nonempty) ∧
          ∀ K ∈ edgeCopySourceSector
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1)),
            edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0 ∉ K := by
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
  rcases
      exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_zero_noPredecessor_noContaining_incrementInserted_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
        (β := β) hβpos (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (m0 := m0) (m1 := m1) hedge hcell_pair hm01
        hemptyResidualPoint hinnerResidualPoint with
    hcover | hhard
  · exact Or.inl hcover
  · right
    rcases hhard with ⟨m, hm, hmzero, hnoPred, hnoContaining⟩
    refine ⟨m, hm, ?_, hmzero, hnoPred, ?_⟩
    · simpa [w] using hactive_of_pair m hm
    · exact
        (edgeCopySourceSectorContainingCopy_not_nonempty_iff_forall_not_mem
          (G := FK.boxGraph 3 (2 * n))
          (A := doubledBoxOriginToInnerEndpointSource n v)
          (m := Function.update m e0 (m e0 + 1))
          (i := edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).mp
          hnoContaining

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_active_zero_noPredecessor_canonicalDeletionMem_allSwitchedRowsAvoidIncrementInserted_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
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
    (hemptyResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768)
    (hinnerResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew ∨
      ∃ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ∧
          m e0 = 0 ∧
          (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              m).Nonempty) ∧
          let G := FK.boxGraph 3 (2 * n)
          let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
          let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
            edgeCopyIncrementInserted G m e0
          let deletion : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \
              {inserted}
          deletion ∈ edgeCopySourceSector G
              (doubledBoxOriginToInnerEndpointSource n v) M ∧
            inserted ∉ deletion ∧
            ∀ K ∈ edgeCopySourceSector G
                (doubledBoxOriginToInnerEndpointSource n v) M,
              inserted ∉ K := by
  classical
  rcases
      exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_active_zero_noPredecessor_allSwitchedRowsAvoidIncrementInserted_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
        (β := β) hβpos (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (m0 := m0) (m1 := m1) hedge hcell_pair hm01
        hemptyResidualPoint hinnerResidualPoint with
    hcover | hhard
  · exact Or.inl hcover
  · right
    rcases hhard with ⟨m, hm, hactive, hmzero, hnoPred, havoidAll⟩
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
      edgeCopyIncrementInserted G m e0
    let deletion : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \ {inserted}
    have hdelete_mem :
        deletion ∈ edgeCopySourceSector G
            (doubledBoxOriginToInnerEndpointSource n v) M := by
      simpa [G, M, inserted, deletion] using
        doubledBoxIncrementedFullSourceActive_selectedEdgeDeletion_mem_switchedSourceSector_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos
          (e0 := e0) (m := m) hedge hactive
          (i := inserted) (by simp [inserted, edgeCopyIncrementInserted])
    have hdelete_avoid : inserted ∉ deletion := by
      simp [deletion]
    have havoidAll' :
        ∀ K ∈ edgeCopySourceSector G
            (doubledBoxOriginToInnerEndpointSource n v) M,
          inserted ∉ K := by
      simpa [G, M, inserted] using havoidAll
    refine ⟨m, hm, hactive, hmzero, hnoPred, ?_⟩
    exact ⟨hdelete_mem, hdelete_avoid, havoidAll'⟩

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_active_zero_noPredecessor_canonicalDeletionMem_switchedSourceSector_eq_excludingIncrementInserted_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
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
    (hemptyResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768)
    (hinnerResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew ∨
      ∃ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ∧
          m e0 = 0 ∧
          (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              m).Nonempty) ∧
          let G := FK.boxGraph 3 (2 * n)
          let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
          let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
            edgeCopyIncrementInserted G m e0
          let deletion : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \
              {inserted}
          deletion ∈ edgeCopySourceSector G
              (doubledBoxOriginToInnerEndpointSource n v) M ∧
            inserted ∉ deletion ∧
            edgeCopySourceSector G (doubledBoxOriginToInnerEndpointSource n v) M =
              edgeCopySourceSectorExcludingCopy G
                (doubledBoxOriginToInnerEndpointSource n v) M inserted := by
  classical
  rcases
      exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_active_zero_noPredecessor_canonicalDeletionMem_allSwitchedRowsAvoidIncrementInserted_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
        (β := β) hβpos (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (m0 := m0) (m1 := m1) hedge hcell_pair hm01
        hemptyResidualPoint hinnerResidualPoint with
    hcover | hhard
  · exact Or.inl hcover
  · right
    rcases hhard with
      ⟨m, hm, hactive, hmzero, hnoPred, hdeletion, hdeleteAvoid,
        havoidAll⟩
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
      edgeCopyIncrementInserted G m e0
    let deletion : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \ {inserted}
    have hdeletion' :
        deletion ∈ edgeCopySourceSector G
            (doubledBoxOriginToInnerEndpointSource n v) M := by
      simpa [G, M, inserted, deletion] using hdeletion
    have hdeleteAvoid' : inserted ∉ deletion := by
      simp [deletion]
    have havoidAll' :
        ∀ K ∈ edgeCopySourceSector G
            (doubledBoxOriginToInnerEndpointSource n v) M,
          inserted ∉ K := by
      simpa [G, M, inserted] using havoidAll
    have heq :
        edgeCopySourceSector G (doubledBoxOriginToInnerEndpointSource n v) M =
          edgeCopySourceSectorExcludingCopy G
            (doubledBoxOriginToInnerEndpointSource n v) M inserted :=
      edgeCopySourceSector_eq_excludingCopy_of_forall_not_mem havoidAll'
    refine ⟨m, hm, hactive, hmzero, hnoPred, ?_⟩
    exact ⟨hdeletion', hdeleteAvoid', heq⟩

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_active_ownerMismatch_zero_noPredecessor_canonicalDeletionMem_excludingIncrementInsertedNonempty_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
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
    (hemptyResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768)
    (hinnerResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew ∨
      ∃ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ∧
          doubledBoxOriginIncidentOwner n m = some ew ∧
          ew ≠ e0 ∧
          m e0 = 0 ∧
          (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              m).Nonempty) ∧
          let G := FK.boxGraph 3 (2 * n)
          let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
          let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
            edgeCopyIncrementInserted G m e0
          let deletion : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \
              {inserted}
          deletion ∈ edgeCopySourceSector G
              (doubledBoxOriginToInnerEndpointSource n v) M ∧
            inserted ∉ deletion ∧
            deletion ∈ edgeCopySourceSectorExcludingCopy G
              (doubledBoxOriginToInnerEndpointSource n v) M inserted ∧
            0 < (edgeCopySourceSectorExcludingCopy G
              (doubledBoxOriginToInnerEndpointSource n v) M inserted).card ∧
            edgeCopySourceSector G (doubledBoxOriginToInnerEndpointSource n v) M =
              edgeCopySourceSectorExcludingCopy G
                (doubledBoxOriginToInnerEndpointSource n v) M inserted := by
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
  have howner_of_pair :
      ∀ m ∈ ({m0, m1} : Finset Profile),
        doubledBoxOriginIncidentOwner n m = some ew := by
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
    exact (Finset.mem_filter.mp hmfilter).2.2
  rcases
      exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_active_zero_noPredecessor_canonicalDeletionMem_switchedSourceSector_eq_excludingIncrementInserted_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
        (β := β) hβpos (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (m0 := m0) (m1 := m1) hedge hcell_pair hm01
        hemptyResidualPoint hinnerResidualPoint with
    hcover | hhard
  · exact Or.inl hcover
  · right
    rcases hhard with
      ⟨m, hm, hactive, hmzero, hnoPred, hdeletion, _hdeleteAvoid,
        heq⟩
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
      edgeCopyIncrementInserted G m e0
    let deletion : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \ {inserted}
    have howner : doubledBoxOriginIncidentOwner n m = some ew := by
      simpa [Profile] using howner_of_pair m hm
    have howner_ne : ew ≠ e0 :=
      doubledBoxOriginIncidentOwner_ne_selectedEdge_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge howner
    have hdeletion_source :
        deletion ∈ edgeCopySourceSector G
            (doubledBoxOriginToInnerEndpointSource n v) M := by
      simpa [G, M, inserted, deletion] using hdeletion
    have hdelete_avoid : inserted ∉ deletion := by
      simp [deletion]
    have hdeletion_excluding :
        deletion ∈ edgeCopySourceSectorExcludingCopy G
            (doubledBoxOriginToInnerEndpointSource n v) M inserted :=
      (mem_edgeCopySourceSectorExcludingCopy
        (G := G) (A := doubledBoxOriginToInnerEndpointSource n v)
        (m := M) (i := inserted) (K := deletion)).mpr
        ⟨hdeletion_source, hdelete_avoid⟩
    have hcard_pos :
        0 < (edgeCopySourceSectorExcludingCopy G
            (doubledBoxOriginToInnerEndpointSource n v) M inserted).card :=
      edgeCopySourceSectorExcludingCopy_card_pos_of_mem
        (G := G) (A := doubledBoxOriginToInnerEndpointSource n v)
        (m := M) (i := inserted) (K := deletion)
        hdeletion_source hdelete_avoid
    have heq' :
        edgeCopySourceSector G (doubledBoxOriginToInnerEndpointSource n v) M =
          edgeCopySourceSectorExcludingCopy G
            (doubledBoxOriginToInnerEndpointSource n v) M inserted := by
      simpa [G, M, inserted] using heq
    refine
      ⟨m, hm, hactive, howner, howner_ne, hmzero, hnoPred, ?_⟩
    exact
      ⟨hdeletion_source, hdelete_avoid, hdeletion_excluding, hcard_pos, heq'⟩

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_active_ownerMismatch_zero_noPredecessor_canonicalDeletionOutsideCurrentMem_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
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
    (hemptyResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768)
    (hinnerResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew ∨
      ∃ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ∧
          doubledBoxOriginIncidentOwner n m = some ew ∧
          ew ≠ e0 ∧
          m e0 = 0 ∧
          (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              m).Nonempty) ∧
          let G := FK.boxGraph 3 (2 * n)
          let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
          let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
            edgeCopyIncrementInserted G m e0
          let deletion : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \
              {inserted}
          let outsidePair :
            Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
              Sharpness.FluxEdgeCopy.Copy G M) := ⟨deletion, inserted⟩
          deletion ∈ edgeCopySourceSector G
              (doubledBoxOriginToInnerEndpointSource n v) M ∧
            inserted ∉ deletion ∧
            deletion ∈ edgeCopySourceSectorExcludingCopy G
              (doubledBoxOriginToInnerEndpointSource n v) M inserted ∧
            0 < (edgeCopySourceSectorExcludingCopy G
              (doubledBoxOriginToInnerEndpointSource n v) M inserted).card ∧
            outsidePair ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
              G (doubledBoxOriginToInnerEndpointSource n v) M e0 ∧
            0 < (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
              G (doubledBoxOriginToInnerEndpointSource n v) M e0).card ∧
            edgeCopySourceSector G (doubledBoxOriginToInnerEndpointSource n v) M =
              edgeCopySourceSectorExcludingCopy G
                (doubledBoxOriginToInnerEndpointSource n v) M inserted := by
  classical
  rcases
      exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_active_ownerMismatch_zero_noPredecessor_canonicalDeletionMem_excludingIncrementInsertedNonempty_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
        (β := β) hβpos (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (m0 := m0) (m1 := m1) hedge hcell_pair hm01
        hemptyResidualPoint hinnerResidualPoint with
    hcover | hhard
  · exact Or.inl hcover
  · right
    rcases hhard with
      ⟨m, hm, hactive, howner, howner_ne, hmzero, hnoPred,
        hdeletion, _hdeleteAvoid, hdeletionExcluding, hexcludingCard,
        heq⟩
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
      edgeCopyIncrementInserted G m e0
    let deletion : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \ {inserted}
    let outsidePair :
        Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
          Sharpness.FluxEdgeCopy.Copy G M) := ⟨deletion, inserted⟩
    have hdeletion_source :
        deletion ∈ edgeCopySourceSector G
            (doubledBoxOriginToInnerEndpointSource n v) M := by
      simpa [G, M, inserted, deletion] using hdeletion
    have hdelete_avoid : inserted ∉ deletion := by
      simp [deletion]
    have hdeletion_excluding :
        deletion ∈ edgeCopySourceSectorExcludingCopy G
            (doubledBoxOriginToInnerEndpointSource n v) M inserted := by
      simpa [G, M, inserted, deletion] using hdeletionExcluding
    have hexcluding_card :
        0 < (edgeCopySourceSectorExcludingCopy G
            (doubledBoxOriginToInnerEndpointSource n v) M inserted).card := by
      simpa [G, M, inserted] using hexcludingCard
    have hpairs :
        outsidePair ∈ edgeCopySourceSectorSelectedEdgeCopyPairs G
            (doubledBoxOriginToInnerEndpointSource n v) M e0 := by
      exact
        (edgeCopySourceSectorSelectedEdgeCopyPairs_mem G
          (doubledBoxOriginToInnerEndpointSource n v) M e0 outsidePair).mpr
          ⟨hdeletion_source,
            by simp [outsidePair, inserted, edgeCopyIncrementInserted]⟩
    have houtsidePair :
        outsidePair ∈
          edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
            (doubledBoxOriginToInnerEndpointSource n v) M e0 := by
      exact
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem G
          (doubledBoxOriginToInnerEndpointSource n v) M e0 outsidePair).mpr
          ⟨hpairs, by simpa [outsidePair] using hdelete_avoid⟩
    have houtside_card :
        0 < (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
            (doubledBoxOriginToInnerEndpointSource n v) M e0).card :=
      Finset.Nonempty.card_pos ⟨outsidePair, houtsidePair⟩
    have heq' :
        edgeCopySourceSector G (doubledBoxOriginToInnerEndpointSource n v) M =
          edgeCopySourceSectorExcludingCopy G
            (doubledBoxOriginToInnerEndpointSource n v) M inserted := by
      simpa [G, M, inserted] using heq
    refine
      ⟨m, hm, hactive, howner, howner_ne, hmzero, hnoPred, ?_⟩
    exact
      ⟨hdeletion_source, hdelete_avoid, hdeletion_excluding,
        hexcluding_card, houtsidePair, houtside_card, heq'⟩

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_active_updateSelectedEdgeMultiplicity_ownerMismatch_zero_noPredecessor_canonicalDeletionOutsideCurrentMem_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
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
    (hemptyResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768)
    (hinnerResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew ∨
      ∃ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        m ∈
            (Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) ∧
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ∧
          doubledBoxOriginIncidentOwner n m = some ew ∧
          ew ∈ doubledBoxOriginIncidentEdges n ∧
          ew ≠ e0 ∧
          m ew ≠ 0 ∧
          (Function.update m e0 (m e0 + 1)) ew ≠ 0 ∧
          m e0 = 0 ∧
          (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              m).Nonempty) ∧
          let G := FK.boxGraph 3 (2 * n)
          let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
          let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
            edgeCopyIncrementInserted G m e0
          let deletion : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \
              {inserted}
          let outsidePair :
            Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
              Sharpness.FluxEdgeCopy.Copy G M) := ⟨deletion, inserted⟩
          deletion ∈ edgeCopySourceSector G
              (doubledBoxOriginToInnerEndpointSource n v) M ∧
            inserted ∉ deletion ∧
            deletion ∈ edgeCopySourceSectorExcludingCopy G
              (doubledBoxOriginToInnerEndpointSource n v) M inserted ∧
            0 < (edgeCopySourceSectorExcludingCopy G
              (doubledBoxOriginToInnerEndpointSource n v) M inserted).card ∧
            outsidePair ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
              G (doubledBoxOriginToInnerEndpointSource n v) M e0 ∧
            0 < (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
              G (doubledBoxOriginToInnerEndpointSource n v) M e0).card ∧
            edgeCopySourceSector G (doubledBoxOriginToInnerEndpointSource n v) M =
              edgeCopySourceSectorExcludingCopy G
                (doubledBoxOriginToInnerEndpointSource n v) M inserted := by
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
  have hΩactive_of_pair :
      ∀ m ∈ ({m0, m1} : Finset Profile), m ∈ Ωactive := by
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
    exact (Finset.mem_filter.mp hmfilter).1
  rcases
      exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_active_ownerMismatch_zero_noPredecessor_canonicalDeletionOutsideCurrentMem_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
        (β := β) hβpos (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (m0 := m0) (m1 := m1) hedge hcell_pair hm01
        hemptyResidualPoint hinnerResidualPoint with
    hcover | hhard
  · exact Or.inl hcover
  · right
    rcases hhard with
      ⟨m, hm, hactive, howner, howner_ne, hmzero, hnoPred,
        hdeletion, hdeleteAvoid, hdeletionExcluding, hexcludingCard,
        houtsidePair, houtsideCard, heq⟩
    have howner_spec :
        ew ∈ doubledBoxOriginIncidentEdges n ∧ m ew ≠ 0 :=
      doubledBoxOriginIncidentOwner_spec_of_eq_some
        (n := n) (m := m) (e := ew) howner
    have hupdate_pos :
        (Function.update m e0 (m e0 + 1)) ew ≠ 0 := by
      simpa [Function.update, howner_ne] using howner_spec.2
    have hupdate_mem :
        m ∈
          (Ω.filter
            (doubledBoxIncrementedFullSourceActive n w e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) := by
      exact Finset.mem_filter.mpr
        ⟨by simpa [Ωactive] using hΩactive_of_pair m hm,
          by simpa [w] using hupdate_pos⟩
    refine
      ⟨m, hm, ?_, hactive, howner, howner_spec.1, howner_ne,
        howner_spec.2, hupdate_pos, hmzero, hnoPred, ?_⟩
    · simpa [w] using hupdate_mem
    · exact
        ⟨hdeletion, hdeleteAvoid, hdeletionExcluding, hexcludingCard,
          houtsidePair, houtsideCard, heq⟩

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_active_supportPatternMem_ownerMem_updateSelectedEdgeMultiplicity_ownerMismatch_zero_noPredecessor_canonicalDeletionOutsideCurrentMem_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
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
    (hemptyResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768)
    (hinnerResidualPoint :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          ((β / 6) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
                  (if m = m0 then m1 else m0))) /
            768) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew ∨
      ∃ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        m ∈
            (Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
              (fun m =>
                doubledBoxOriginIncidentSupport n m = S ∧
                  doubledBoxOriginIncidentOwner n m = some ew) ∧
          m ∈
            (Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) ∧
          doubledBoxOriginIncidentSupport n m = S ∧
          S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
            (fun S => S.Nonempty) ∧
          ew ∈ S ∧
          doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ∧
          doubledBoxOriginIncidentOwner n m = some ew ∧
          ew ∈ doubledBoxOriginIncidentEdges n ∧
          ew ≠ e0 ∧
          m ew ≠ 0 ∧
          (Function.update m e0 (m e0 + 1)) ew ≠ 0 ∧
          m e0 = 0 ∧
          (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              m).Nonempty) ∧
          let G := FK.boxGraph 3 (2 * n)
          let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
          let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
            edgeCopyIncrementInserted G m e0
          let deletion : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \
              {inserted}
          let outsidePair :
            Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
              Sharpness.FluxEdgeCopy.Copy G M) := ⟨deletion, inserted⟩
          deletion ∈ edgeCopySourceSector G
              (doubledBoxOriginToInnerEndpointSource n v) M ∧
            inserted ∉ deletion ∧
            deletion ∈ edgeCopySourceSectorExcludingCopy G
              (doubledBoxOriginToInnerEndpointSource n v) M inserted ∧
            0 < (edgeCopySourceSectorExcludingCopy G
              (doubledBoxOriginToInnerEndpointSource n v) M inserted).card ∧
            outsidePair ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
              G (doubledBoxOriginToInnerEndpointSource n v) M e0 ∧
            0 < (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
              G (doubledBoxOriginToInnerEndpointSource n v) M e0).card ∧
            edgeCopySourceSector G (doubledBoxOriginToInnerEndpointSource n v) M =
              edgeCopySourceSectorExcludingCopy G
                (doubledBoxOriginToInnerEndpointSource n v) M inserted := by
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
  have hcell_mem_of_pair :
      ∀ m ∈ ({m0, m1} : Finset Profile), m ∈ cell := by
    intro m hm
    rw [hcell]
    exact hm
  rcases
      exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_active_updateSelectedEdgeMultiplicity_ownerMismatch_zero_noPredecessor_canonicalDeletionOutsideCurrentMem_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
        (β := β) hβpos (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (m0 := m0) (m1 := m1) hedge hcell_pair hm01
        hemptyResidualPoint hinnerResidualPoint with
    hcover | hhard
  · exact Or.inl hcover
  · right
    rcases hhard with
      ⟨m, hm, hupdateMem, hactive, howner, hewOrigin, howner_ne,
        hmew, hupdate_pos, hmzero, hnoPred, hdeletion, hdeleteAvoid,
        hdeletionExcluding, hexcludingCard, houtsidePair, houtsideCard,
        heq⟩
    have hmcell : m ∈ cell := hcell_mem_of_pair m hm
    have hmcell' :
        m ∈
          (Ω.filter
            (doubledBoxIncrementedFullSourceActive n w e0)).filter
            (fun m =>
              doubledBoxOriginIncidentSupport n m = S ∧
                doubledBoxOriginIncidentOwner n m = some ew) := by
      simpa [cell, Ωactive] using hmcell
    have hsupport : doubledBoxOriginIncidentSupport n m = S :=
      (Finset.mem_filter.mp hmcell').2.1
    have hewSupport : ew ∈ doubledBoxOriginIncidentSupport n m :=
      mem_doubledBoxOriginIncidentSupport.mpr ⟨hewOrigin, hmew⟩
    have hewS : ew ∈ S := by
      simpa [hsupport] using hewSupport
    have hSnonempty : S.Nonempty := ⟨ew, hewS⟩
    have hSpattern :
        S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
            (fun S => S.Nonempty) := by
      exact Finset.mem_filter.mpr
        ⟨by
          rw [← hsupport]
          exact doubledBoxOriginIncidentSupport_mem_originIncidentEdges_powerset,
          hSnonempty⟩
    refine
      ⟨m, hm, ?_, hupdateMem, hsupport, hSpattern, hewS, hactive,
        howner, hewOrigin, howner_ne, hmew, hupdate_pos, hmzero, hnoPred,
        ?_⟩
    · simpa [w] using hmcell'
    · exact
        ⟨hdeletion, hdeleteAvoid, hdeletionExcluding, hexcludingCard,
          houtsidePair, houtsideCard, heq⟩

end Exact3D
end StatMech
