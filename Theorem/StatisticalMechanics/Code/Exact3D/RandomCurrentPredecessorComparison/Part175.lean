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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part167
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsAt_of_empty_same_pos
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
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsAt
        β n := by
  intro hcontract
  exact
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionAt_of_empty_same_pos
      (β := β) (n := n) (v := v) (hvwedge := hvwedge) (hlt := hlt)
      (hypos := hypos) (e0 := e0) (hedge := hedge) hβ hsame
      (hcontract v hvwedge hlt hypos e0 hedge)

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsAt_of_inner_same_pos
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
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsAt
        β n := by
  intro hcontract
  exact
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionAt_of_inner_same_pos
      (β := β) (n := n) (v := v) (hvwedge := hvwedge) (hlt := hlt)
      (hypos := hypos) (e0 := e0) (hedge := hedge) hβ hsame
      (hcontract v hvwedge hlt hypos e0 hedge)

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionAt_of_empty_strictSectorYPredecessorRow3
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
    (hcontract :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionAt
        β n v hvwedge hlt hypos e0 hedge) :
    False :=
  not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionAt_of_empty_same_pos
    (β := β) (n := n) (v := v) (hvwedge := hvwedge) (hlt := hlt)
    (hypos := hypos) (e0 := e0) (hedge := hedge) hβ
    (doubledBoxOriginToInnerEndpointSourcePairEmptySum_pos_of_strictSectorYPredecessorRow3
      hβ v hvwedge hlt hypos)
    hcontract

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionAt_of_inner_strictSectorYPredecessor3
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
    (hcontract :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionAt
        β n v hvwedge hlt hypos e0 hedge) :
    False :=
  not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionAt_of_inner_same_pos
    (β := β) (n := n) (v := v) (hvwedge := hvwedge) (hlt := hlt)
    (hypos := hypos) (e0 := e0) (hedge := hedge) hβ
    (doubledBoxOriginToInnerEndpointInnerPairSourcePairSum_pos_of_strictSectorYPredecessor3
      hβ v hvwedge hlt hypos)
    hcontract

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsAt_of_empty_strictSectorYPredecessorRow3
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
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsAt
        β n :=
  not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsAt_of_empty_same_pos
    (β := β) (n := n) (v := v) (hvwedge := hvwedge) (hlt := hlt)
    (hypos := hypos) (e0 := e0) hβ hedge
    (doubledBoxOriginToInnerEndpointSourcePairEmptySum_pos_of_strictSectorYPredecessorRow3
      hβ v hvwedge hlt hypos)

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsAt_of_inner_strictSectorYPredecessor3
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
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsAt
        β n :=
  not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsAt_of_inner_same_pos
    (β := β) (n := n) (v := v) (hvwedge := hvwedge) (hlt := hlt)
    (hypos := hypos) (e0 := e0) hβ hedge
    (doubledBoxOriginToInnerEndpointInnerPairSourcePairSum_pos_of_strictSectorYPredecessor3
      hβ v hvwedge hlt hypos)

end Exact3D
end StatMech
