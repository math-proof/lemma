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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part112
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

open Classical in
set_option linter.style.longLine false in


theorem DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowDomain_supportOwnerCell_mem
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hm :
      m ∈
        DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowDomain
          hvwedge hlt hypos e0 Ω S ew) :
    m ∈
      DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowSupportOwnerCell
        hvwedge hlt hypos e0 Ω S ew := by
  classical
  simpa [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowDomain] using
    (Finset.mem_filter.mp hm).1

open Classical in
set_option linter.style.longLine false in


theorem DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowDomain_updateSelectedEdgeMultiplicityCell_mem
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hm :
      m ∈
        DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowDomain
          hvwedge hlt hypos e0 Ω S ew) :
    m ∈
      DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowUpdateSelectedEdgeMultiplicityCell
        hvwedge hlt hypos e0 Ω ew := by
  classical
  have hcell :
      m ∈
        DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowSupportOwnerCell
          hvwedge hlt hypos e0 Ω S ew :=
    DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowDomain_supportOwnerCell_mem
      hm
  have hactive :
      m ∈
        Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0) := by
    simpa
      [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowSupportOwnerCell]
      using (Finset.mem_filter.mp hcell).1
  have hupdate :
      (Function.update m e0 (m e0 + 1)) ew ≠ 0 := by
    simpa [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowDomain]
      using (Finset.mem_filter.mp hm).2
  exact
    Finset.mem_filter.mpr
      ⟨by
        simpa
          [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowUpdateSelectedEdgeMultiplicityCell]
          using hactive,
        hupdate⟩

open Classical in
set_option linter.style.longLine false in

theorem DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow_mem_domain
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hrow :
      DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow
        hvwedge hlt hypos e0 Ω S ew m) :
    m ∈
      DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowDomain
        hvwedge hlt hypos e0 Ω S ew := by
  classical
  have hcell :
      m ∈
        DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowSupportOwnerCell
          hvwedge hlt hypos e0 Ω S ew := by
    simpa
      [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowSupportOwnerCell,
        DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow]
      using hrow.1
  have hupdate :
      (Function.update m e0 (m e0 + 1)) ew ≠ 0 := by
    have hupdateMem :
        m ∈
          (Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) := by
      simpa [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow] using
        hrow.2.1
    exact
      (Finset.mem_filter.mp hupdateMem).2
  exact
    Finset.mem_filter.mpr
      ⟨by
        simpa
          [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowDomain]
          using hcell,
        hupdate⟩

open Classical in
set_option linter.style.longLine false in


theorem DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow_supportOwnerCell_mem
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hrow :
      DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow
        hvwedge hlt hypos e0 Ω S ew m) :
    m ∈
      (Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew) := by
  classical
  simpa [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow] using
    hrow.1

open Classical in
set_option linter.style.longLine false in


theorem DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow_updateSelectedEdgeMultiplicity_mem
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hrow :
      DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow
        hvwedge hlt hypos e0 Ω S ew m) :
    m ∈
      (Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) := by
  classical
  simpa [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow] using
    hrow.2.1

open Classical in
set_option linter.style.longLine false in


theorem DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow_support_eq
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hrow :
      DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow
        hvwedge hlt hypos e0 Ω S ew m) :
    doubledBoxOriginIncidentSupport n m = S := by
  classical
  simpa [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow] using
    hrow.2.2.1

open Classical in
set_option linter.style.longLine false in


theorem DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow_supportPattern_mem
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hrow :
      DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow
        hvwedge hlt hypos e0 Ω S ew m) :
    S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
      (fun S => S.Nonempty) := by
  classical
  simpa [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow] using
    hrow.2.2.2.1

open Classical in
set_option linter.style.longLine false in


theorem DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow_owner_mem_support
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hrow :
      DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow
        hvwedge hlt hypos e0 Ω S ew m) :
    ew ∈ S := by
  classical
  simpa [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow] using
    hrow.2.2.2.2.1

open Classical in
set_option linter.style.longLine false in


theorem DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow_supportPattern_card_le_six
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hrow :
      DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow
        hvwedge hlt hypos e0 Ω S ew m) :
    S.card ≤ 6 :=
  doubledBoxNonemptyOriginIncidentSupportPattern_card_le_six
    (n := n) (S := S)
    (DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow_supportPattern_mem
      hrow)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_indexedHardRow_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
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
        DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow
          hvwedge hlt hypos e0 Ω S ew m := by
  classical
  rcases
      exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_active_supportPatternMem_ownerMem_updateSelectedEdgeMultiplicity_ownerMismatch_zero_noPredecessor_canonicalDeletionOutsideCurrentMem_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
        (β := β) hβpos (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (m0 := m0) (m1 := m1) hedge hcell_pair hm01
        hemptyResidualPoint hinnerResidualPoint with
    hcover | hhard
  · exact Or.inl hcover
  · right
    rcases hhard with
      ⟨m, hm, hcellMem, hupdateMem, hsupport, hSpattern, hewS,
        hactive, howner, hewOrigin, howner_ne, hmew, hupdate_pos,
        hmzero, hnoPred, hdeletion, hdeleteAvoid, hdeletionExcluding,
        hexcludingCard, houtsidePair, houtsideCard, heq⟩
    refine ⟨m, hm, ?_⟩
    exact
      ⟨hcellMem, hupdateMem, hsupport, hSpattern, hewS, hactive,
        howner, hewOrigin, howner_ne, hmew, hupdate_pos, hmzero,
        hnoPred, hdeletion, hdeleteAvoid, hdeletionExcluding,
        hexcludingCard, houtsidePair, houtsideCard, heq⟩

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_no_indexedHardRow_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
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
            768)
    (hnoHard :
      ∀ m ∈ ({m0, m1} :
          Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)),
        ¬ DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow
          hvwedge hlt hypos e0 Ω S ew m) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  rcases
      exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_or_exists_indexedHardRow_of_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
        (β := β) hβpos (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (m0 := m0) (m1 := m1) hedge hcell_pair hm01
        hemptyResidualPoint hinnerResidualPoint with
    hcover | hhard
  · exact hcover
  · rcases hhard with ⟨m, hm, hrow⟩
    exact False.elim ((hnoHard m hm) hrow)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_no_indexedHardRow_supportOwner_updateFilter_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
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
            768)
    (hnoHard :
      ∀ m,
        m ∈
          (Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m =>
              doubledBoxOriginIncidentSupport n m = S ∧
                doubledBoxOriginIncidentOwner n m = some ew) →
        m ∈
          (Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) →
        ¬ DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow
          hvwedge hlt hypos e0 Ω S ew m) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  refine
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_no_indexedHardRow_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
      (β := β) hβpos (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01
      hemptyResidualPoint hinnerResidualPoint ?_
  intro m _hm hrow
  exact
    (hnoHard m
      (DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow_supportOwnerCell_mem
        hrow)
      (DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow_updateSelectedEdgeMultiplicity_mem
        hrow)) hrow

open Classical in
set_option linter.style.longLine false in

theorem DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow_noHardRow_of_table_eq_empty
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (htable :
      DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowTable
        hvwedge hlt hypos e0 Ω S ew = ∅) :
    ∀ m,
      m ∈
        (Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
      m ∈
        (Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) →
      ¬ DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow
        hvwedge hlt hypos e0 Ω S ew m := by
  classical
  intro m hsupport hupdate hrow
  have hsupportCell :
      m ∈
        DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowSupportOwnerCell
          hvwedge hlt hypos e0 Ω S ew := by
    simpa
      [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowSupportOwnerCell]
      using hsupport
  have hupdatePred :
      (Function.update m e0 (m e0 + 1)) ew ≠ 0 :=
    (Finset.mem_filter.mp hupdate).2
  have hdomain :
      m ∈
        DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowDomain
          hvwedge hlt hypos e0 Ω S ew := by
    have hdomain' :
        m ∈
          (DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowSupportOwnerCell
            hvwedge hlt hypos e0 Ω S ew).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) :=
      Finset.mem_filter.mpr ⟨hsupportCell, hupdatePred⟩
    simpa [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowDomain]
      using hdomain'
  have htableMem :
      m ∈
        DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowTable
          hvwedge hlt hypos e0 Ω S ew := by
    simpa [DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowTable]
      using Finset.mem_filter.mpr ⟨hdomain, hrow⟩
  rw [htable] at htableMem
  simp at htableMem

open Classical in
set_option linter.style.longLine false in

theorem DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow_noHardRow_of_table_card_eq_zero
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcard :
      (DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowTable
        hvwedge hlt hypos e0 Ω S ew).card = 0) :
    ∀ m,
      m ∈
        (Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
      m ∈
        (Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) →
      ¬ DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow
        hvwedge hlt hypos e0 Ω S ew m :=
  DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow_noHardRow_of_table_eq_empty
    (Finset.card_eq_zero.mp hcard)

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_indexedHardRowTable_eq_empty_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
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
            768)
    (htable :
      DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowTable
        hvwedge hlt hypos e0 Ω S ew = ∅) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  refine
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_no_indexedHardRow_supportOwner_updateFilter_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
      (β := β) hβpos (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (m0 := m0) (m1 := m1) hedge hcell_pair hm01
      hemptyResidualPoint hinnerResidualPoint ?_
  exact
    DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRow_noHardRow_of_table_eq_empty
      htable

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_indexedHardRowTable_card_eq_zero_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
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
            768)
    (hcard :
      (DoubledBoxStrictSectorYSupportPatternOwnerIndexedHardRowTable
        hvwedge hlt hypos e0 Ω S ew).card = 0) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew :=
  exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_indexedHardRowTable_eq_empty_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
    (β := β) hβpos (n := n) hvwedge hlt hypos
    (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
    (m0 := m0) (m1 := m1) hedge hcell_pair hm01
    hemptyResidualPoint hinnerResidualPoint (Finset.card_eq_zero.mp hcard)

open Classical in
set_option linter.style.longLine false in

theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_noHardRowFiniteEnumerationCertificate_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
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
            768)
    (hcert :
      DoubledBoxStrictSectorYSupportPatternOwnerIndexedNoHardRowFiniteEnumerationCertificate
        hvwedge hlt hypos e0 Ω S ew) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew :=
  exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt_of_indexedHardRowTable_eq_empty_cell_eq_pair_swappedSelectedDeletion_residualMomentDiv768Pointwise
    (β := β) hβpos (n := n) hvwedge hlt hypos
    (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
    (m0 := m0) (m1 := m1) hedge hcell_pair hm01
    hemptyResidualPoint hinnerResidualPoint hcert

open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellRouteShareBoundsAt_of_coverRouteShareBoundsAt
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
      ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew ∧
      ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt]
    at hcover
  rcases hcover with
    ⟨rows, hcell_subset, hemptyData, hinnerData⟩
  rcases hemptyData with
    ⟨emptyProfileRouteRows, emptyWitnessRows, hempty_inj, hempty_left,
      hempty_right, hempty_point⟩
  rcases hinnerData with
    ⟨innerProfileRouteRows, innerWitnessRows, hinner_inj, hinner_left,
      hinner_right, hinner_point⟩
  constructor
  · exact
      exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt_of_cell_subset_finset
        (β := β) (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (rows := rows) hcell_subset emptyProfileRouteRows emptyWitnessRows
        hempty_inj hempty_left hempty_right hempty_point
  · exact
      exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_of_cell_subset_finset
        (β := β) (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (rows := rows) hcell_subset innerProfileRouteRows innerWitnessRows
        hinner_inj hinner_left hinner_right hinner_point

set_option maxHeartbeats 900000 in


open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt_of_emptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
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
      ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let Profile := ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt]
    at hsource
  rcases hsource with
    ⟨rows, hcell_subset, hemptyData, hinnerData⟩
  rcases hemptyData with
    ⟨emptyProfileRouteRows, emptyWitnessRows, hemptyInj, hemptyLeft,
      hemptyRight, hemptyPoint⟩
  rcases hinnerData with
    ⟨innerProfileRouteRows, innerWitnessRows, hinnerInj, hinnerLeft,
      hinnerRight, hinnerPoint⟩
  let emptySplitRows : {m : Profile // m ∈ rows} → Finset Unit :=
    fun _ => {()}
  let emptyProfileRouteSplitRows :
      (m : {m : Profile // m ∈ rows}) → Unit → Profile :=
    fun m _ => emptyProfileRouteRows m
  let emptyWitnessSplitRows :
      (m : {m : Profile // m ∈ rows}) → (i : Unit) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (emptyProfileRouteSplitRows m i)) :=
    fun m _ => emptyWitnessRows m
  have hemptyLeftSplit :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (emptyProfileRouteSplitRows m i))
          (emptyWitnessSplitRows m i) =
          doubledBoxOriginToInnerEndpointSource n v := by
    intro m i
    cases i
    simpa [emptyProfileRouteSplitRows, emptyWitnessSplitRows] using
      hemptyLeft m
  have hemptyRightSplit :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (emptyProfileRouteSplitRows m i))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n))
                  (emptyProfileRouteSplitRows m i))) \
            emptyWitnessSplitRows m i) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
    intro m i
    cases i
    simpa [emptyProfileRouteSplitRows, emptyWitnessSplitRows] using
      hemptyRight m
  have hemptySplitInj :
      Set.InjOn
        (fun p : Sigma (fun _ : {m : Profile // m ∈ rows} => Unit) =>
          emptyProfileRouteSplitRows p.1 p.2)
        (rows.attach.sigma emptySplitRows) := by
    intro p hp q hq hroute
    rcases p with ⟨p, pi⟩
    rcases q with ⟨q, qi⟩
    cases pi
    cases qi
    simpa [emptyProfileRouteSplitRows] using hemptyInj hroute
  have hemptySplitPoint :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
            ∑ i ∈ emptySplitRows ⟨m, hm⟩,
              ((β / 6) *
                Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (Sharpness.ofEdgeFun
                    (FK.boxGraph 3 (2 * n))
                    (emptyProfileRouteSplitRows ⟨m, hm⟩ i))) /
                384 := by
    intro m hm
    simpa [emptySplitRows, emptyProfileRouteSplitRows] using
      hemptyPoint m hm
  let innerSplitRows : {m : Profile // m ∈ rows} → Finset Unit :=
    fun _ => {()}
  let innerProfileRouteSplitRows :
      (m : {m : Profile // m ∈ rows}) → Unit → Profile :=
    fun m _ => innerProfileRouteRows m
  let innerWitnessSplitRows :
      (m : {m : Profile // m ∈ rows}) → (i : Unit) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (innerProfileRouteSplitRows m i)) :=
    fun m _ => innerWitnessRows m
  have hinnerLeftSplit :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (innerProfileRouteSplitRows m i))
          (innerWitnessSplitRows m i) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
    intro m i
    cases i
    simpa [innerProfileRouteSplitRows, innerWitnessSplitRows] using
      hinnerLeft m
  have hinnerRightSplit :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (innerProfileRouteSplitRows m i))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n))
                  (innerProfileRouteSplitRows m i))) \
            innerWitnessSplitRows m i) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
    intro m i
    cases i
    simpa [innerProfileRouteSplitRows, innerWitnessSplitRows] using
      hinnerRight m
  have hinnerSplitInj :
      Set.InjOn
        (fun p : Sigma (fun _ : {m : Profile // m ∈ rows} => Unit) =>
          innerProfileRouteSplitRows p.1 p.2)
        (rows.attach.sigma innerSplitRows) := by
    intro p hp q hq hroute
    rcases p with ⟨p, pi⟩
    rcases q with ⟨q, qi⟩
    cases pi
    cases qi
    simpa [innerProfileRouteSplitRows] using hinnerInj hroute
  have hinnerSplitPoint :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m ≤
            ∑ i ∈ innerSplitRows ⟨m, hm⟩,
              ((β / 6) *
                Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (Sharpness.ofEdgeFun
                    (FK.boxGraph 3 (2 * n))
                    (innerProfileRouteSplitRows ⟨m, hm⟩ i))) /
                384 := by
    intro m hm
    simpa [innerSplitRows, innerProfileRouteSplitRows] using
      hinnerPoint m hm
  exact
    exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt_of_cell_subset_finset_sourceEquation
      (β := β) (n := n) hvwedge hlt hypos
      (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
      (rows := rows) (by simpa [Profile] using hcell_subset)
      emptySplitRows emptyProfileRouteSplitRows emptyWitnessSplitRows
      hemptyLeftSplit hemptyRightSplit hemptySplitInj hemptySplitPoint
      innerSplitRows innerProfileRouteSplitRows innerWitnessSplitRows
      hinnerLeftSplit hinnerRightSplit hinnerSplitInj hinnerSplitPoint

set_option maxHeartbeats 900000 in


open Classical in
set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt_of_emptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
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
      ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt
      β n v hvwedge hlt hypos e0 Ω S ew := by
  classical
  let Profile := ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt]
    at hsource
  rcases hsource with
    ⟨rows, hcell_subset, hemptyData, hinnerData⟩
  rcases hemptyData with
    ⟨emptyProfileRouteRows, emptyWitnessRows, hemptyInj, hemptyLeft,
      hemptyRight, hemptyPoint⟩
  rcases hinnerData with
    ⟨innerProfileRouteRows, innerWitnessRows, hinnerInj, hinnerLeft,
      hinnerRight, hinnerPoint⟩
  let emptySplitRows : {m : Profile // m ∈ rows} → Finset Unit :=
    fun _ => {()}
  let emptyProfileRouteSplitRows :
      (m : {m : Profile // m ∈ rows}) → Unit → Profile :=
    fun m _ => emptyProfileRouteRows m
  let emptyWitnessSplitRows :
      (m : {m : Profile // m ∈ rows}) → (i : Unit) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (emptyProfileRouteSplitRows m i)) :=
    fun m _ => emptyWitnessRows m
  have hemptyLeftSplit :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (emptyProfileRouteSplitRows m i))
          (emptyWitnessSplitRows m i) =
          doubledBoxOriginToInnerEndpointSource n v := by
    intro m i
    cases i
    simpa [emptyProfileRouteSplitRows, emptyWitnessSplitRows] using
      hemptyLeft m
  have hemptyRightSplit :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (emptyProfileRouteSplitRows m i))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n))
                  (emptyProfileRouteSplitRows m i))) \
            emptyWitnessSplitRows m i) =
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
    intro m i
    cases i
    simpa [emptyProfileRouteSplitRows, emptyWitnessSplitRows] using
      hemptyRight m
  have hemptySplitInj :
      Set.InjOn
        (fun p : Sigma (fun _ : {m : Profile // m ∈ rows} => Unit) =>
          emptyProfileRouteSplitRows p.1 p.2)
        (rows.attach.sigma emptySplitRows) := by
    intro p _hp q _hq hroute
    rcases p with ⟨p, pi⟩
    rcases q with ⟨q, qi⟩
    cases pi
    cases qi
    simpa [emptyProfileRouteSplitRows] using hemptyInj hroute
  have hemptySplitPoint :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
            ∑ i ∈ emptySplitRows ⟨m, hm⟩,
              ((β / 6) *
                Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (Sharpness.ofEdgeFun
                    (FK.boxGraph 3 (2 * n))
                    (emptyProfileRouteSplitRows ⟨m, hm⟩ i))) /
                384 := by
    intro m hm
    simpa [emptySplitRows, emptyProfileRouteSplitRows] using
      hemptyPoint m hm
  let innerSplitRows : {m : Profile // m ∈ rows} → Finset Unit :=
    fun _ => {()}
  let innerProfileRouteSplitRows :
      (m : {m : Profile // m ∈ rows}) → Unit → Profile :=
    fun m _ => innerProfileRouteRows m
  let innerWitnessSplitRows :
      (m : {m : Profile // m ∈ rows}) → (i : Unit) →
        Finset
          (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) (innerProfileRouteSplitRows m i)) :=
    fun m _ => innerWitnessRows m
  have hinnerLeftSplit :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (innerProfileRouteSplitRows m i))
          (innerWitnessSplitRows m i) =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
    intro m i
    cases i
    simpa [innerProfileRouteSplitRows, innerWitnessSplitRows] using
      hinnerLeft m
  have hinnerRightSplit :
      ∀ m i,
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (FK.boxGraph 3 (2 * n)) (innerProfileRouteSplitRows m i))
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n))
                  (innerProfileRouteSplitRows m i))) \
            innerWitnessSplitRows m i) =
          doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
    intro m i
    cases i
    simpa [innerProfileRouteSplitRows, innerWitnessSplitRows] using
      hinnerRight m
  have hinnerSplitInj :
      Set.InjOn
        (fun p : Sigma (fun _ : {m : Profile // m ∈ rows} => Unit) =>
          innerProfileRouteSplitRows p.1 p.2)
        (rows.attach.sigma innerSplitRows) := by
    intro p _hp q _hq hroute
    rcases p with ⟨p, pi⟩
    rcases q with ⟨q, qi⟩
    cases pi
    cases qi
    simpa [innerProfileRouteSplitRows] using hinnerInj hroute
  have hinnerSplitPoint :
      ∀ m,
        ∀ hm : m ∈ rows,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m ≤
            ∑ i ∈ innerSplitRows ⟨m, hm⟩,
              ((β / 6) *
                Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (Sharpness.ofEdgeFun
                    (FK.boxGraph 3 (2 * n))
                    (innerProfileRouteSplitRows ⟨m, hm⟩ i))) /
                384 := by
    intro m hm
    simpa [innerSplitRows, innerProfileRouteSplitRows] using
      hinnerPoint m hm
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt]
  refine ⟨rows, ?_, ?_, ?_⟩
  · simpa [Profile] using hcell_subset
  · exact
      ⟨Unit, emptySplitRows, emptyProfileRouteSplitRows,
        emptyWitnessSplitRows, hemptyLeftSplit, hemptyRightSplit,
        hemptySplitInj, hemptySplitPoint⟩
  · exact
      ⟨Unit, innerSplitRows, innerProfileRouteSplitRows,
        innerWitnessSplitRows, hinnerLeftSplit, hinnerRightSplit,
        hinnerSplitInj, hinnerSplitPoint⟩

end Exact3D
end StatMech
