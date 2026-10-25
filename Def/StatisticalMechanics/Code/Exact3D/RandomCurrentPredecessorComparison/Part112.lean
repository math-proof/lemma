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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part119
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

open Classical in
set_option linter.style.longLine false in


def DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) : Prop :=
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
    edgeCopyIncrementInserted G m e0
  let deletion : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
    (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \ {inserted}
  let outsidePair :
      Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
        Sharpness.FluxEdgeCopy.Copy G M) := ⟨deletion, inserted⟩
  m ∈
      (Ω.filter
        (doubledBoxIncrementedFullSourceActive n w e0)).filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) ∧
    m ∈
      (Ω.filter
        (doubledBoxIncrementedFullSourceActive n w e0)).filter
        (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) ∧
    doubledBoxOriginIncidentSupport n m = S ∧
    S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
      (fun S => S.Nonempty) ∧
    ew ∈ S ∧
    doubledBoxIncrementedFullSourceActive n w e0 m ∧
    doubledBoxOriginIncidentOwner n m = some ew ∧
    ew ∈ doubledBoxOriginIncidentEdges n ∧
    ew ≠ e0 ∧
    m ew ≠ 0 ∧
    (Function.update m e0 (m e0 + 1)) ew ≠ 0 ∧
    m e0 = 0 ∧
    (¬ (edgeCopySourceSector G
        (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
    deletion ∈ edgeCopySourceSector G
        (doubledBoxOriginToInnerEndpointSource n v) M ∧
    inserted ∉ deletion ∧
    deletion ∈ edgeCopySourceSectorExcludingCopy G
        (doubledBoxOriginToInnerEndpointSource n v) M inserted ∧
    0 < (edgeCopySourceSectorExcludingCopy G
        (doubledBoxOriginToInnerEndpointSource n v) M inserted).card ∧
    outsidePair ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
        (doubledBoxOriginToInnerEndpointSource n v) M e0 ∧
    0 < (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
        (doubledBoxOriginToInnerEndpointSource n v) M e0).card ∧
    edgeCopySourceSector G (doubledBoxOriginToInnerEndpointSource n v) M =
      edgeCopySourceSectorExcludingCopy G
        (doubledBoxOriginToInnerEndpointSource n v) M inserted

open Classical in
set_option linter.style.longLine false in


noncomputable def DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowSupportOwnerCell
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :=
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  (Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
    (fun m =>
      doubledBoxOriginIncidentSupport n m = S ∧
        doubledBoxOriginIncidentOwner n m = some ew)

open Classical in
set_option linter.style.longLine false in


noncomputable def DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowUpdateSelectedEdgeMultiplicityCell
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :=
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  (Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
    (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)

open Classical in
set_option linter.style.longLine false in


noncomputable def DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowDomain
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :=
  (DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowSupportOwnerCell
    hvwedge hlt hypos e0 Ω S ew).filter
    (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)

open Classical in
set_option linter.style.longLine false in


noncomputable def DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowTable
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :=
  (DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowDomain
    hvwedge hlt hypos e0 Ω S ew).filter
    (fun m =>
      DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow
        hvwedge hlt hypos e0 Ω S ew m)

open Classical in
set_option linter.style.longLine false in


def DoubledBoxStrictSectorYSupportPatternOwnerIndexedNoHardRowFiniteEnumerationCertificate
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
  DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowTable
    hvwedge hlt hypos e0 Ω S ew = ∅

end Exact3D
end StatMech
