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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part87
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem fourBetaSixthScalarContraction_not_of_same_pos_le_four
    {β same four : ℝ} (hβ : 0 < β) (hsame : 0 < same)
    (hle : same ≤ four) :
    ¬ ((2 * β) * four ≤ (β * same) / 6) := by
  intro hcontract
  have hmono : (2 * β) * same ≤ (2 * β) * four := by
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  have hbad : (2 * β) * same ≤ (β * same) / 6 :=
    hmono.trans hcontract
  nlinarith [hβ, hsame, hbad]

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt_of_empty_same_pos_le_four
    {β : ℝ} (hβ : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
          s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
            FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hsame :
      0 < doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v)
    (hle :
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v ≤
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n)))) :
    ¬
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt
        β n := by
  intro hcontract
  exact
    fourBetaSixthScalarContraction_not_of_same_pos_le_four hβ hsame hle
      ((hcontract v hvwedge hlt hypos e0 hedge).1)

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt_of_inner_same_pos_le_four
    {β : ℝ} (hβ : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
          s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
            FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hsame :
      0 <
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hle :
      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) ≤
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    ¬
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt
        β n := by
  intro hcontract
  exact
    fourBetaSixthScalarContraction_not_of_same_pos_le_four hβ hsame hle
      ((hcontract v hvwedge hlt hypos e0 hedge).2)

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt_of_empty_same_pos
    {β : ℝ} (hβ : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
          s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
            FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hsame :
      0 < doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) :
    ¬
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt
        β n := by
  have hβfour : β ≤ 2 * (2 * β) := by nlinarith [hβ]
  have hle :
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v ≤
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
    simpa [doubledBoxOriginToInnerEndpointSourcePairEmptySum] using
      sourcePairSum_mono_beta (FK.boxGraph 3 (2 * n)) hβ.le hβfour
        (fun _ => 1) (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n)))
  exact
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt_of_empty_same_pos_le_four
      hβ hedge hsame hle

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt_of_inner_same_pos
    {β : ℝ} (hβ : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
          s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
            FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hsame :
      0 <
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    ¬
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt
        β n := by
  have hβfour : β ≤ 2 * (2 * β) := by nlinarith [hβ]
  have hle :
      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) ≤
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) := by
    exact
      sourcePairSum_mono_beta (FK.boxGraph 3 (2 * n)) hβ.le hβfour
        (fun _ => 1) (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
        (doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
  exact
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt_of_inner_same_pos_le_four
      hβ hedge hsame hle

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt_of_empty_strictSectorYPredecessorRow3
    {β : ℝ} (hβ : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
          s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
            FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    ¬
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt
        β n :=
  not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt_of_empty_same_pos
    (β := β) (n := n) (v := v) (hvwedge := hvwedge) (hlt := hlt)
    (hypos := hypos) (e0 := e0) hβ hedge
    (doubledBoxOriginToInnerEndpointSourcePairEmptySum_pos_of_strictSectorYPredecessorRow3
      hβ v hvwedge hlt hypos)

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt_of_inner_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
          s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
            FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    ¬
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt
        β n :=
  not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt_of_inner_same_pos
    (β := β) (n := n) (v := v) (hvwedge := hvwedge) (hlt := hlt)
    (hypos := hypos) (e0 := e0) hβ hedge
    (doubledBoxOriginToInnerEndpointInnerPairSourcePairSum_pos_of_strictSectorYPredecessor3
      hβ v hvwedge hlt hypos)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseSixthRelaxedExplicitCaseTableFiniteBudgetAt_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hcontract :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseSixthRelaxedExplicitCaseTableFiniteBudgetAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Profile := ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let Ωowner : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset Profile :=
    fun ew => Ωactive.filter
      (fun m => doubledBoxOriginIncidentOwner n m = some ew)
  let emptyRow : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  let innerRow : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m
  have hcontractLocal := hcontract v hvwedge hlt hypos e0 hedge
  refine
    ⟨Profile, Ωowner, (fun _ m => m), (fun _ m => emptyRow m),
      (fun _ m => innerRow m), (fun _ m => emptyRow m),
      (fun _ m => innerRow m), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ew _hew m hm
    simpa [Ωowner, Ωactive, w] using hm
  · intro ew _hew m hm
    rfl
  · intro ew _hew m hm
    rfl
  · intro ew _hew c hc
    rfl
  · intro ew _hew c hc
    rfl
  · intro ew _hew
    change
      finiteSupportExplicitCaseBudgetTotal (Ωowner ew) (fun m => m)
          (Ωowner ew) emptyRow ≤
        (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6
    calc
      finiteSupportExplicitCaseBudgetTotal (Ωowner ew) (fun m => m)
          (Ωowner ew) emptyRow =
          ∑ m ∈ Ωowner ew, emptyRow m := by
        rw [finiteSupportExplicitCaseBudgetTotal_self_eq_finset_sum]
      _ ≤
          (2 * β) *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n))
              (2 * (2 * β)) (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
        simpa [emptyRow] using
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_finset_sum_coarse_le_two_beta_mul_four_beta_sharpnessSourcePairSum
            hβ n v w e0 (Ωowner ew)
      _ ≤
          (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6 := by
        simpa [w] using hcontractLocal.1
  · intro ew _hew
    change
      finiteSupportExplicitCaseBudgetTotal (Ωowner ew) (fun m => m)
          (Ωowner ew) innerRow ≤
        (β *
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) / 6
    calc
      finiteSupportExplicitCaseBudgetTotal (Ωowner ew) (fun m => m)
          (Ωowner ew) innerRow =
          ∑ m ∈ Ωowner ew, innerRow m := by
        rw [finiteSupportExplicitCaseBudgetTotal_self_eq_finset_sum]
      _ ≤
          (2 * β) *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n))
              (2 * (2 * β)) (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) := by
        simpa [innerRow] using
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_finset_sum_coarse_le_two_beta_mul_four_beta_sharpnessSourcePairSum
            hβ n v w e0 (Ωowner ew)
      _ ≤
          (β *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) / 6 := by
        simpa [w] using hcontractLocal.2

end Exact3D
end StatMech
