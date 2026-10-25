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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part166
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem twoFourScalarContraction_not_of_same_pos_le_four
    {same four : ℝ} (hsame : 0 < same) (hle : same ≤ four) :
    ¬ (2 * four ≤ same) := by
  intro hcontract
  have hmono : 2 * same ≤ 2 * four := by
    exact mul_le_mul_of_nonneg_left hle (by norm_num)
  have hbad : 2 * same ≤ same := hmono.trans hcontract
  nlinarith [hsame, hbad]

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionAt_of_empty_same_pos
    {β : ℝ} (hβ : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {hedge :
      e0.1 =
          s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
            FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))}
    (hsame :
      0 < doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) :
    ¬
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionAt
        β n v hvwedge hlt hypos e0 hedge := by
  intro hcontract
  have hβfour : β ≤ 2 * (2 * β) := by nlinarith [hβ]
  have hle :
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v ≤
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
    calc
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v =
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
        rfl
      _ ≤
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
        sourcePairSum_mono_beta (FK.boxGraph 3 (2 * n)) hβ.le hβfour
          (fun _ => 1) (by intro e; norm_num)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n)))
      _ =
          edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
        sourcePairSum_eq_edgeCopySourcePairSum (FK.boxGraph 3 (2 * n))
          (2 * (2 * β)) (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n)))
  exact twoFourScalarContraction_not_of_same_pos_le_four hsame hle hcontract.1

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionAt_of_inner_same_pos
    {β : ℝ} (hβ : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {hedge :
      e0.1 =
          s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
            FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))}
    (hsame :
      0 <
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    ¬
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionAt
        β n v hvwedge hlt hypos e0 hedge := by
  intro hcontract
  have hβfour : β ≤ 2 * (2 * β) := by nlinarith [hβ]
  have hle :
      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) ≤
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) := by
    calc
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
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) :=
        sourcePairSum_mono_beta (FK.boxGraph 3 (2 * n)) hβ.le hβfour
          (fun _ => 1) (by intro e; norm_num)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
      _ =
          edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            (doubledBoxInnerPairSource n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) :=
        sourcePairSum_eq_edgeCopySourcePairSum (FK.boxGraph 3 (2 * n))
          (2 * (2 * β)) (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
  exact twoFourScalarContraction_not_of_same_pos_le_four hsame hle hcontract.2

end Exact3D
end StatMech
