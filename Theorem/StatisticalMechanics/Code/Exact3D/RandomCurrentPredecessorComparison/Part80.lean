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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part72
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originTouchesEdgeSupport_of_edge_not_origin
    {n : ℕ} {w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (he0origin : IsingFK.boxOrigin 3 (2 * n) ∉ e0.1)
    (hactive : doubledBoxIncrementedFullSourceActive n w e0 m) :
    doubledBoxOriginTouchesEdgeSupport n m := by
  classical
  by_contra hnot
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let o := IsingFK.boxOrigin 3 (2 * n)
  have habsent :
      ∀ e : ↥G.edgeFinset, m e ≠ 0 → o ∉ e.1 := by
    simpa [G, o] using
      doubledBoxOrigin_absent_on_edge_support_of_not_originTouchesEdgeSupport
        (n := n) (m := m) hnot
  have hnot_source :
      o ∉
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G M)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G M)) := by
    refine
      randomCurrent_not_mem_sources_of_forall_not_mem_ends
        (Sharpness.FluxEdgeCopy.endsM G M)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) o ?_
    intro i _hi
    have hMpos : M i.1 ≠ 0 := by
      have hlt : (i.2 : ℕ) < M i.1 := i.2.isLt
      omega
    by_cases hie : i.1 = e0
    · have hends :
          Sharpness.FluxEdgeCopy.endsM G M i = e0.1 := by
        simp [Sharpness.FluxEdgeCopy.endsM, hie]
      simpa [hends, o] using he0origin
    · have hmpos : m i.1 ≠ 0 := by
        simpa [M, Function.update_of_ne hie] using hMpos
      simpa [Sharpness.FluxEdgeCopy.endsM, G, o] using habsent i.1 hmpos
  have horigin_source :
      o ∈ doubledBoxOriginToInnerEndpointSource n w := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair how]
    simp [o]
  have horigin_incremented :
      o ∈
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G M)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G M)) := by
    rw [hactive]
    exact horigin_source
  exact hnot_source horigin_incremented

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originTouchesEdgeSupport_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) :
    doubledBoxOriginTouchesEdgeSupport n m := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
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
    ⟨_edge, _hedge, hov, how, _hvw⟩
  have he0origin : IsingFK.boxOrigin 3 (2 * n) ∉ e0.1 := by
    rw [hedge]
    simp [Sym2.mem_iff, hov, how, w]
  exact
    doubledBoxIncrementedFullSourceActive_originTouchesEdgeSupport_of_edge_not_origin
      (n := n) (w := w) (e0 := e0) (m := m) how he0origin
      (by simpa [w] using hactive)

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_filter_originTouchesEdgeSupport_eq_self_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] :
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    ((Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
        (fun m => doubledBoxOriginTouchesEdgeSupport n m)) =
      Ω.filter (doubledBoxIncrementedFullSourceActive n w e0) := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  ext m
  constructor
  · intro hm
    exact (Finset.mem_filter.mp hm).1
  · intro hm
    rw [Finset.mem_filter]
    exact
      ⟨hm,
        doubledBoxIncrementedFullSourceActive_originTouchesEdgeSupport_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
          hedge (by simpa [w] using (Finset.mem_filter.mp hm).2)⟩

set_option linter.style.longLine false in


theorem doubledBoxOrigin_not_mem_strictSectorYPredecessorEdge3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    IsingFK.boxOrigin 3 (2 * n) ∉ e0.1 := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
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
    ⟨_edge, _hedge, hov, how, _hvw⟩
  rw [hedge]
  simp [Sym2.mem_iff, hov, how, w]

set_option linter.style.longLine false in


theorem doubledBoxIncrementedSelectedEdgeInsertedCopy_exists
    {n : ℕ}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    ∃ i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)),
      i.1 = e0 ∧ (i.2 : ℕ) = m e0 := by
  refine ⟨⟨e0, ⟨m e0, ?_⟩⟩, rfl, rfl⟩
  have hlt_succ : m e0 < m e0 + 1 := Nat.lt_succ_self (m e0)
  simp [Function.update, hlt_succ]

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_selectedEdgeDeletion_mem_switchedSourceSector_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
      (Function.update m e0 (m e0 + 1))}
    (hi : i.1 = e0) :
    ((Finset.univ :
      Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)))) \ {i}) ∈
      edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
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
  rw [mem_edgeCopySourceSector]
  have hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G M)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa [G, M, w] using hactive
  have hends :
      Sharpness.FluxEdgeCopy.endsM G M i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) := by
    have hends_eq : Sharpness.FluxEdgeCopy.endsM G M i = i.1.1 := by
      simp [Sharpness.FluxEdgeCopy.endsM, G, M]
    rw [hends_eq, hi]
    simpa [w] using hedge
  have hsingle :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G M)
          ({i} : Finset (Sharpness.FluxEdgeCopy.Copy G M)) =
        doubledBoxInnerPairSource n v w := by
    simpa [doubledBoxInnerPairSource, G] using
      randomCurrent_sources_singleton_of_ends_eq
        (Sharpness.FluxEdgeCopy.endsM G M) hends
  rw [randomCurrent_sources_univ_sdiff, hfull, hsingle]
  exact
    doubledBoxOriginToInnerEndpointSource_symmDiff_innerPair_eq_left
      (n := n) (v := v) (w := w) hov how hvw

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_switchedSourceSector_nonempty_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1))).Nonempty := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let i : Sharpness.FluxEdgeCopy.Copy G M :=
    ⟨e0, ⟨m e0, by
      have hlt_succ : m e0 < m e0 + 1 := Nat.lt_succ_self (m e0)
      simp [M, hlt_succ]⟩⟩
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
  refine
    ⟨(Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \ {i}, ?_⟩
  rw [mem_edgeCopySourceSector]
  have hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G M)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa [G, M, w] using hactive
  have hends :
      Sharpness.FluxEdgeCopy.endsM G M i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) := by
    simpa [Sharpness.FluxEdgeCopy.endsM, G, M, i, w] using hedge
  have hsingle :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G M)
          ({i} : Finset (Sharpness.FluxEdgeCopy.Copy G M)) =
        doubledBoxInnerPairSource n v w := by
    simpa [doubledBoxInnerPairSource, G] using
      randomCurrent_sources_singleton_of_ends_eq
        (Sharpness.FluxEdgeCopy.endsM G M) hends
  rw [randomCurrent_sources_univ_sdiff, hfull, hsingle]
  exact
    doubledBoxOriginToInnerEndpointSource_symmDiff_innerPair_eq_left
      (n := n) (v := v) (w := w) hov how hvw

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_switchedSourceSector_card_pos_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) :
    0 <
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1))).card :=
  Finset.Nonempty.card_pos
    (doubledBoxIncrementedFullSourceActive_switchedSourceSector_nonempty_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
      hedge hactive)

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_sources_univ_original_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)) =
      doubledBoxOriginToInnerEndpointSource n v := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let i : Sharpness.FluxEdgeCopy.Copy G M :=
    ⟨e0, ⟨m e0, by
      have hlt_succ : m e0 < m e0 + 1 := Nat.lt_succ_self (m e0)
      simp [M, hlt_succ]⟩⟩
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
  have hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G M)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa [G, M, w] using hactive
  have hends :
      Sharpness.FluxEdgeCopy.endsM G M i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) := by
    simpa [Sharpness.FluxEdgeCopy.endsM, G, M, i, w] using hedge
  have hsrc_decremented :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G
            (Function.update M i.1 (M i.1 - 1)))
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G
              (Function.update M i.1 (M i.1 - 1)))) =
        doubledBoxOriginToInnerEndpointSource n v := by
    simpa [G, M, i, w] using
      doubledBox_sources_univ_preimageErase_innerPairCopy
        (n := n) (v := v) (w := w) M i hfull hends hov how hvw
  have hprofile : Function.update M i.1 (M i.1 - 1) = m := by
    dsimp [i]
    exact edgeMultiplicityIncrement_decrement_eq m e0
  rw [hprofile] at hsrc_decremented
  simpa [G] using hsrc_decremented

set_option linter.style.longLine false in


theorem doubledBoxInnerPairSource_excluding_incrementInserted_card_pos_iff_switchedSource_containing_incrementInserted_card_pos_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (_hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    0 <
        (edgeCopySourceSectorExcludingCopy G
          (doubledBoxInnerPairSource n v w) M
          (edgeCopyIncrementInserted G m e0)).card ↔
      0 <
        (edgeCopySourceSectorContainingCopy G
          (doubledBoxOriginToInnerEndpointSource n v) M
          (edgeCopyIncrementInserted G m e0)).card := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
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
  have hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G M)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa [G, M, w] using hactive
  have htoggle :
      doubledBoxOriginToInnerEndpointSource n w ∆
          doubledBoxInnerPairSource n v w =
        doubledBoxOriginToInnerEndpointSource n v :=
    doubledBoxOriginToInnerEndpointSource_symmDiff_innerPair_eq_left
      (n := n) (v := v) (w := w) hov how hvw
  have hiff :=
    edgeCopySourceSectorExcludingCopy_card_pos_iff_containingCopy_card_pos_of_univ_source
      (G := G) (A := doubledBoxInnerPairSource n v w)
      (C := doubledBoxOriginToInnerEndpointSource n w) (m := M)
      (i := edgeCopyIncrementInserted G m e0) hfull
  simpa [G, M, w, htoggle] using hiff

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_incrementInserted_excluding_owner_card_le_selectedEdgeOutsideCurrent_innerPairSource_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (owner :
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1))) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    (edgeCopySourceSectorContainingAndExcludingCopy G
        (doubledBoxOriginToInnerEndpointSource n v) M
        (edgeCopyIncrementInserted G m e0) owner).card ≤
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
        (doubledBoxInnerPairSource n v w) M e0).card := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
    edgeCopyIncrementInserted G m e0
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
  have hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G M)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa [G, M, w] using hactive
  have hsource :
      doubledBoxOriginToInnerEndpointSource n w ∆
          doubledBoxOriginToInnerEndpointSource n v =
        doubledBoxInnerPairSource n v w := by
    rw [symmDiff_comm]
    exact
      doubledBoxOriginToInnerEndpointSource_symmDiff_source_eq_innerPair
        (n := n) (v := v) (w := w) hov how hvw
  have hcard_eq :
      (edgeCopySourceSectorContainingAndExcludingCopy G
          (doubledBoxOriginToInnerEndpointSource n v) M inserted owner).card =
        (edgeCopySourceSectorContainingAndExcludingCopy G
          (doubledBoxInnerPairSource n v w) M owner inserted).card := by
    have h :=
      edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_card_eq
        (G := G) (A := doubledBoxOriginToInnerEndpointSource n v)
        (C := doubledBoxOriginToInnerEndpointSource n w) (m := M)
        (inside := inserted) (outside := owner) hfull
    rw [hsource] at h
    exact h
  have hselected_edge : inserted.1 = e0 := by
    simp [inserted, edgeCopyIncrementInserted]
  have hright :
      (edgeCopySourceSectorContainingAndExcludingCopy G
          (doubledBoxInnerPairSource n v w) M owner inserted).card ≤
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
          (doubledBoxInnerPairSource n v w) M e0).card :=
    edgeCopySourceSectorContainingAndExcludingCopy_card_le_selectedEdgeCopyPairsOutsideCurrent_card
      G (doubledBoxInnerPairSource n v w) M e0 owner inserted hselected_edge
  simpa [G, M, w, inserted] using hcard_eq.trans_le hright

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_incrementInserted_excluding_owner_card_mul_le_selectedEdgeOutsideCurrent_innerPairSource_card_mul_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (owner :
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)))
    (base : ℝ) (hbase : 0 ≤ base) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    ((edgeCopySourceSectorContainingAndExcludingCopy G
        (doubledBoxOriginToInnerEndpointSource n v) M
        (edgeCopyIncrementInserted G m e0) owner).card : ℝ) * base ≤
      ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
        (doubledBoxInnerPairSource n v w) M e0).card : ℝ) * base := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  have hcard :
      (edgeCopySourceSectorContainingAndExcludingCopy G
          (doubledBoxOriginToInnerEndpointSource n v) M
          (edgeCopyIncrementInserted G m e0) owner).card ≤
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
          (doubledBoxInnerPairSource n v w) M e0).card := by
    simpa [G, M, w] using
      doubledBoxIncrementedFullSourceActive_incrementInserted_excluding_owner_card_le_selectedEdgeOutsideCurrent_innerPairSource_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
        hactive owner
  have hcard_real :
      ((edgeCopySourceSectorContainingAndExcludingCopy G
          (doubledBoxOriginToInnerEndpointSource n v) M
          (edgeCopyIncrementInserted G m e0) owner).card : ℝ) ≤
        ((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
          (doubledBoxInnerPairSource n v w) M e0).card : ℝ) := by
    exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right hcard_real hbase

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxIncrementedFullSourceActive_incrementInserted_excluding_owner_card_mul_le_selectedEdgeOutsideCurrent_innerPairSource_card_mul_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (owner :
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)))
    (base : ℝ) (hbase : 0 ≤ base) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    β *
        (((edgeCopySourceSectorContainingAndExcludingCopy G
          (doubledBoxOriginToInnerEndpointSource n v) M
          (edgeCopyIncrementInserted G m e0) owner).card : ℝ) * base) ≤
      β *
        (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
          (doubledBoxInnerPairSource n v w) M e0).card : ℝ) * base) := by
  classical
  exact
    mul_le_mul_of_nonneg_left
      (doubledBoxIncrementedFullSourceActive_incrementInserted_excluding_owner_card_mul_le_selectedEdgeOutsideCurrent_innerPairSource_card_mul_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
        hactive owner base hbase)
      hβ

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_one_le_switchedSourceSector_card_cast_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) :
    (1 : ℝ) ≤
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) := by
  have hpos :
      0 <
        (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card :=
    doubledBoxIncrementedFullSourceActive_switchedSourceSector_card_pos_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
      hedge hactive
  exact_mod_cast Nat.succ_le_of_lt hpos

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_filter_eq_biUnion_originIncidentOwnerFilters_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0) =
      (doubledBoxOriginIncidentEdges n).biUnion fun ew =>
        (Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew) := by
  classical
  ext m
  constructor
  · intro hm
    rw [Finset.mem_biUnion]
    have htouch :
        doubledBoxOriginTouchesEdgeSupport n m :=
      doubledBoxIncrementedFullSourceActive_originTouchesEdgeSupport_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
        hedge (by simpa using (Finset.mem_filter.mp hm).2)
    rcases
        doubledBoxOriginIncidentOwner_exists_of_originTouchesEdgeSupport
          (n := n) (m := m) htouch with
      ⟨ew, hew, howner, _hmew⟩
    refine ⟨ew, hew, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hm, howner⟩
  · intro hm
    rw [Finset.mem_biUnion] at hm
    rcases hm with ⟨ew, _hew, hmew⟩
    exact (Finset.mem_filter.mp hmew).1

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentEdge_ne_strictSectorYPredecessorEdge3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hew : ew ∈ doubledBoxOriginIncidentEdges n) :
    ew ≠ e0 := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
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
    ⟨_edge, _hedge, hov, how, _hvw⟩
  have he0origin : IsingFK.boxOrigin 3 (2 * n) ∉ e0.1 := by
    rw [hedge]
    simp [Sym2.mem_iff, hov, how, w]
  exact
    doubledBoxOriginIncidentEdge_ne_of_origin_not_mem
      (n := n) (e0 := e0) (ew := ew) he0origin hew

set_option linter.style.longLine false in


theorem strictSectorYPredecessorEdge_not_mem_doubledBoxOriginIncidentEdges3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    e0 ∉ doubledBoxOriginIncidentEdges n := by
  intro he0
  exact
    (doubledBoxOriginIncidentEdge_ne_strictSectorYPredecessorEdge3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := e0)
      hedge he0) rfl

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentEdges_filter_ne_strictSectorYPredecessorEdge_eq
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    (doubledBoxOriginIncidentEdges n).filter (fun ew => ew ≠ e0) =
      doubledBoxOriginIncidentEdges n := by
  classical
  ext ew
  constructor
  · intro hew
    exact (Finset.mem_filter.mp hew).1
  · intro hew
    exact
      Finset.mem_filter.mpr
        ⟨hew,
          doubledBoxOriginIncidentEdge_ne_strictSectorYPredecessorEdge3
            (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
            (ew := ew) hedge hew⟩

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentEdges_sum_eq_strictMismatch_sum_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (F : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℝ) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n, F ew) =
      ∑ ew ∈ (doubledBoxOriginIncidentEdges n).filter (fun ew => ew ≠ e0),
        F ew := by
  rw [
    doubledBoxOriginIncidentEdges_filter_ne_strictSectorYPredecessorEdge_eq
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge]

set_option linter.style.longLine false in

theorem doubledBoxOriginIncidentEdges_sum_le_strictMismatch_budget_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {F : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℝ}
    {mismatchBudget : ℝ}
    (hmismatch :
      (∑ ew ∈ (doubledBoxOriginIncidentEdges n).filter (fun ew => ew ≠ e0),
        F ew) ≤ mismatchBudget) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n, F ew) ≤ mismatchBudget := by
  rw [
    doubledBoxOriginIncidentEdges_sum_eq_strictMismatch_sum_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge F]
  exact hmismatch

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupportPattern_edge_ne_selectedEdge_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hS :
      S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
        (fun S => S.Nonempty))
    (hew : ew ∈ S) :
    ew ≠ e0 := by
  have hSsubset : S ⊆ doubledBoxOriginIncidentEdges n := by
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  exact
    doubledBoxOriginIncidentEdge_ne_strictSectorYPredecessorEdge3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge (hSsubset hew)

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentOwner_ne_selectedEdge_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    ew ≠ e0 :=
    doubledBoxOriginIncidentEdge_ne_strictSectorYPredecessorEdge3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge
      (doubledBoxOriginIncidentOwner_spec_of_eq_some
        (n := n) (m := m) (e := ew) howner).1

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_originIncidentOwner_eq_unincrementedMultiplicity_of_strictSectorYPredecessor3
    (β : ℝ) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew m =
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
        (β *
          (((m ew : ℕ) : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) m)) := by
  exact
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_edge_ne_eq_unincrementedMultiplicity
      β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) m
      (doubledBoxOriginIncidentOwner_ne_selectedEdge_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge howner)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_originIncidentOwner_eq_unincrementedMultiplicity_of_strictSectorYPredecessor3
    (β : ℝ) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge β
        n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew m =
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
        (β *
          (((m ew : ℕ) : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              (doubledBoxInnerPairSource n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m)) := by
  exact
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_edge_ne_eq_unincrementedMultiplicity
      β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) m
      (doubledBoxOriginIncidentOwner_ne_selectedEdge_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge howner)

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentOwnerCopy_ne_selectedEdge_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (owner : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
      (Function.update m e0 (m e0 + 1)))
    (hownerEdge : owner.1 = ew)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    owner.1 ≠ e0 := by
  intro hselected
  exact
    (doubledBoxOriginIncidentOwner_ne_selectedEdge_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (m := m) hedge howner)
      (hownerEdge.symm.trans hselected)

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData_originIncidentSupport_mem_of_ne_deletedEdge
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
        (doubledBoxOriginToInnerEndpointSource n w) m e0)
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentSupport n m)
    (hne : ew ≠ p.2.1) :
    ew ∈ doubledBoxOriginIncidentSupport n
      (doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp).1 := by
  change ew ∈ doubledBoxOriginIncidentSupport n
    (Function.update m p.2.1 (m p.2.1 - 1))
  exact mem_doubledBoxOriginIncidentSupport_update_sub_one_of_ne hew hne

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData_originIncidentSupport_mem_of_ne_deletedEdge
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
        (doubledBoxOriginToInnerEndpointSource n w) m e0)
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentSupport n m)
    (hne : ew ≠ p.2.1) :
    ew ∈ doubledBoxOriginIncidentSupport n
      (doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp).1 := by
  change ew ∈ doubledBoxOriginIncidentSupport n
    (Function.update m p.2.1 (m p.2.1 - 1))
  exact mem_doubledBoxOriginIncidentSupport_update_sub_one_of_ne hew hne

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData_originIncidentSupport_eq_of_deletedEdge_not_originIncident
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
        (doubledBoxOriginToInnerEndpointSource n w) m e0)
    (hdel : p.2.1 ∉ doubledBoxOriginIncidentEdges n) :
    doubledBoxOriginIncidentSupport n
        (doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData
          (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp).1 =
      doubledBoxOriginIncidentSupport n m := by
  change doubledBoxOriginIncidentSupport n
      (Function.update m p.2.1 (m p.2.1 - 1)) =
    doubledBoxOriginIncidentSupport n m
  exact
    doubledBoxOriginIncidentSupport_update_sub_one_eq_of_not_mem_originIncidentEdges
      (n := n) (m := m) (del := p.2.1) hdel

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData_originIncidentSupport_eq_of_deletedEdge_not_originIncident
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
        (doubledBoxOriginToInnerEndpointSource n w) m e0)
    (hdel : p.2.1 ∉ doubledBoxOriginIncidentEdges n) :
    doubledBoxOriginIncidentSupport n
        (doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData
          (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp).1 =
      doubledBoxOriginIncidentSupport n m := by
  change doubledBoxOriginIncidentSupport n
      (Function.update m p.2.1 (m p.2.1 - 1)) =
    doubledBoxOriginIncidentSupport n m
  exact
    doubledBoxOriginIncidentSupport_update_sub_one_eq_of_not_mem_originIncidentEdges
      (n := n) (m := m) (del := p.2.1) hdel

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData_originIncidentSupport_mem_of_ne_selectedEdge
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
        (doubledBoxOriginToInnerEndpointSource n w) m e0)
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentSupport n m)
    (hne : ew ≠ e0) :
    ew ∈ doubledBoxOriginIncidentSupport n
      (doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp).1 := by
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) m e0 p).mp hp
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) m e0 p).mp hpbranch.1
  have hdel : ew ≠ p.2.1 := by
    intro heq
    exact hne (heq.trans hpbase.2)
  exact
    doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData_originIncidentSupport_mem_of_ne_deletedEdge
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
      hew hdel

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData_originIncidentSupport_mem_of_ne_selectedEdge
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
        (doubledBoxOriginToInnerEndpointSource n w) m e0)
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentSupport n m)
    (hne : ew ≠ e0) :
    ew ∈ doubledBoxOriginIncidentSupport n
      (doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp).1 := by
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) m e0 p).mp hp
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) m e0 p).mp hpbranch.1
  have hdel : ew ≠ p.2.1 := by
    intro heq
    exact hne (heq.trans hpbase.2)
  exact
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData_originIncidentSupport_mem_of_ne_deletedEdge
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
      hew hdel

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData_originIncidentSupport_mem_of_ne_deletedEdge
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
        (doubledBoxOriginToInnerEndpointSource n v) m e0)
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentSupport n m)
    (hne : ew ≠ p.2.1) :
    ew ∈ doubledBoxOriginIncidentSupport n
      (doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp).1 := by
  change ew ∈ doubledBoxOriginIncidentSupport n
    (Function.update m p.2.1 (m p.2.1 - 1))
  exact mem_doubledBoxOriginIncidentSupport_update_sub_one_of_ne hew hne

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData_originIncidentSupport_mem_of_ne_deletedEdge
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
        (doubledBoxOriginToInnerEndpointSource n v) m e0)
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentSupport n m)
    (hne : ew ≠ p.2.1) :
    ew ∈ doubledBoxOriginIncidentSupport n
      (doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp).1 := by
  change ew ∈ doubledBoxOriginIncidentSupport n
    (Function.update m p.2.1 (m p.2.1 - 1))
  exact mem_doubledBoxOriginIncidentSupport_update_sub_one_of_ne hew hne

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData_originIncidentSupport_eq_of_deletedEdge_not_originIncident
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
        (doubledBoxOriginToInnerEndpointSource n v) m e0)
    (hdel : p.2.1 ∉ doubledBoxOriginIncidentEdges n) :
    doubledBoxOriginIncidentSupport n
        (doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData
          (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp).1 =
      doubledBoxOriginIncidentSupport n m := by
  change doubledBoxOriginIncidentSupport n
      (Function.update m p.2.1 (m p.2.1 - 1)) =
    doubledBoxOriginIncidentSupport n m
  exact
    doubledBoxOriginIncidentSupport_update_sub_one_eq_of_not_mem_originIncidentEdges
      (n := n) (m := m) (del := p.2.1) hdel

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData_originIncidentSupport_eq_of_deletedEdge_not_originIncident
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
        (doubledBoxOriginToInnerEndpointSource n v) m e0)
    (hdel : p.2.1 ∉ doubledBoxOriginIncidentEdges n) :
    doubledBoxOriginIncidentSupport n
        (doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData
          (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp).1 =
      doubledBoxOriginIncidentSupport n m := by
  change doubledBoxOriginIncidentSupport n
      (Function.update m p.2.1 (m p.2.1 - 1)) =
    doubledBoxOriginIncidentSupport n m
  exact
    doubledBoxOriginIncidentSupport_update_sub_one_eq_of_not_mem_originIncidentEdges
      (n := n) (m := m) (del := p.2.1) hdel

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData_originIncidentSupport_mem_of_ne_selectedEdge
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
        (doubledBoxOriginToInnerEndpointSource n v) m e0)
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentSupport n m)
    (hne : ew ≠ e0) :
    ew ∈ doubledBoxOriginIncidentSupport n
      (doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp).1 := by
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v) m e0 p).mp hp
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v) m e0 p).mp hpbranch.1
  have hdel : ew ≠ p.2.1 := by
    intro heq
    exact hne (heq.trans hpbase.2)
  exact
    doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData_originIncidentSupport_mem_of_ne_deletedEdge
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
      hew hdel

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData_originIncidentSupport_mem_of_ne_selectedEdge
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
        (doubledBoxOriginToInnerEndpointSource n v) m e0)
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentSupport n m)
    (hne : ew ≠ e0) :
    ew ∈ doubledBoxOriginIncidentSupport n
      (doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData
        (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp).1 := by
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v) m e0 p).mp hp
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v) m e0 p).mp hpbranch.1
  have hdel : ew ≠ p.2.1 := by
    intro heq
    exact hne (heq.trans hpbase.2)
  exact
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData_originIncidentSupport_mem_of_ne_deletedEdge
      (n := n) (v := v) (w := w) m e0 hedge hfull hov how hvw hp
      hew hdel

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData_originIncidentSupport_mem_of_originIncidentOwner_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (howner : doubledBoxOriginIncidentOwner n m = some ew)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m e0) :
    ew ∈ doubledBoxOriginIncidentSupport n
      (doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData
        (n := n) (v := v)
        (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
        m e0 hedge hfull hov how hvw hp).1 := by
  have hew_support : ew ∈ doubledBoxOriginIncidentSupport n m := by
    exact
      mem_doubledBoxOriginIncidentSupport.mpr
        (doubledBoxOriginIncidentOwner_spec_of_eq_some
          (n := n) (m := m) (e := ew) howner)
  have hne : ew ≠ e0 :=
    doubledBoxOriginIncidentOwner_ne_selectedEdge_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (m := m) hedge howner
  exact
    doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData_originIncidentSupport_mem_of_ne_selectedEdge
      (n := n) (v := v)
      (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
      m e0 hedge hfull hov how hvw hp hew_support hne

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData_originIncidentSupport_mem_of_originIncidentOwner_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (howner : doubledBoxOriginIncidentOwner n m = some ew)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m e0) :
    ew ∈ doubledBoxOriginIncidentSupport n
      (doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData
        (n := n) (v := v)
        (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
        m e0 hedge hfull hov how hvw hp).1 := by
  have hew_support : ew ∈ doubledBoxOriginIncidentSupport n m := by
    exact
      mem_doubledBoxOriginIncidentSupport.mpr
        (doubledBoxOriginIncidentOwner_spec_of_eq_some
          (n := n) (m := m) (e := ew) howner)
  have hne : ew ≠ e0 :=
    doubledBoxOriginIncidentOwner_ne_selectedEdge_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (m := m) hedge howner
  exact
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData_originIncidentSupport_mem_of_ne_selectedEdge
      (n := n) (v := v)
      (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
      m e0 hedge hfull hov how hvw hp hew_support hne

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData_originIncidentSupport_eq_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m e0) :
    doubledBoxOriginIncidentSupport n
        (doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData
          (n := n) (v := v)
          (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          m e0 hedge hfull hov how hvw hp).1 =
      doubledBoxOriginIncidentSupport n m := by
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m e0 p).mp hp
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m e0 p).mp
        hpbranch.1
  have hdel : p.2.1 ∉ doubledBoxOriginIncidentEdges n := by
    intro hpdel
    have he0 : e0 ∈ doubledBoxOriginIncidentEdges n := by
      simpa [hpbase.2] using hpdel
    exact
      (doubledBoxOriginIncidentEdge_ne_strictSectorYPredecessorEdge3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := e0)
        hedge he0) rfl
  exact
    doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData_originIncidentSupport_eq_of_deletedEdge_not_originIncident
      (n := n) (v := v)
      (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
      m e0 hedge hfull hov how hvw hp hdel

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData_originIncidentSupport_eq_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m e0) :
    doubledBoxOriginIncidentSupport n
        (doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData
          (n := n) (v := v)
          (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          m e0 hedge hfull hov how hvw hp).1 =
      doubledBoxOriginIncidentSupport n m := by
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m e0 p).mp hp
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m e0 p).mp
        hpbranch.1
  have hdel : p.2.1 ∉ doubledBoxOriginIncidentEdges n := by
    intro hpdel
    have he0 : e0 ∈ doubledBoxOriginIncidentEdges n := by
      simpa [hpbase.2] using hpdel
    exact
      (doubledBoxOriginIncidentEdge_ne_strictSectorYPredecessorEdge3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := e0)
        hedge he0) rfl
  exact
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData_originIncidentSupport_eq_of_deletedEdge_not_originIncident
      (n := n) (v := v)
      (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
      m e0 hedge hfull hov how hvw hp hdel

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData_originIncidentSupport_eq_singleton_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hsupport : doubledBoxOriginIncidentSupport n m = {ew})
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m e0) :
    doubledBoxOriginIncidentSupport n
        (doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData
          (n := n) (v := v)
          (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          m e0 hedge hfull hov how hvw hp).1 = {ew} := by
  rw [
    doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairData_originIncidentSupport_eq_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos m e0 hedge hfull hov how hvw hp,
    hsupport]

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData_originIncidentSupport_eq_singleton_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hsupport : doubledBoxOriginIncidentSupport n m = {ew})
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m e0) :
    doubledBoxOriginIncidentSupport n
        (doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData
          (n := n) (v := v)
          (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          m e0 hedge hfull hov how hvw hp).1 = {ew} := by
  rw [
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairData_originIncidentSupport_eq_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos m e0 hedge hfull hov how hvw hp,
    hsupport]

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData_originIncidentSupport_eq_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m e0) :
    doubledBoxOriginIncidentSupport n
        (doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData
          (n := n) (v := v)
          (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          m e0 hedge hfull hov how hvw hp).1 =
      doubledBoxOriginIncidentSupport n m := by
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v) m e0 p).mp hp
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v) m e0 p).mp hpbranch.1
  have hdel : p.2.1 ∉ doubledBoxOriginIncidentEdges n := by
    intro hpdel
    have he0 : e0 ∈ doubledBoxOriginIncidentEdges n := by
      simpa [hpbase.2] using hpdel
    exact
      (doubledBoxOriginIncidentEdge_ne_strictSectorYPredecessorEdge3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := e0)
        hedge he0) rfl
  change doubledBoxOriginIncidentSupport n
      (Function.update m p.2.1 (m p.2.1 - 1)) =
    doubledBoxOriginIncidentSupport n m
  exact
    doubledBoxOriginIncidentSupport_update_sub_one_eq_of_not_mem_originIncidentEdges
      (n := n) (m := m) (del := p.2.1) hdel

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData_originIncidentSupport_eq_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m e0) :
    doubledBoxOriginIncidentSupport n
        (doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData
          (n := n) (v := v)
          (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          m e0 hedge hfull hov how hvw hp).1 =
      doubledBoxOriginIncidentSupport n m := by
  have hpbranch :=
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v) m e0 p).mp hp
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v) m e0 p).mp hpbranch.1
  have hdel : p.2.1 ∉ doubledBoxOriginIncidentEdges n := by
    intro hpdel
    have he0 : e0 ∈ doubledBoxOriginIncidentEdges n := by
      simpa [hpbase.2] using hpdel
    exact
      (doubledBoxOriginIncidentEdge_ne_strictSectorYPredecessorEdge3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := e0)
        hedge he0) rfl
  change doubledBoxOriginIncidentSupport n
      (Function.update m p.2.1 (m p.2.1 - 1)) =
    doubledBoxOriginIncidentSupport n m
  exact
    doubledBoxOriginIncidentSupport_update_sub_one_eq_of_not_mem_originIncidentEdges
      (n := n) (m := m) (del := p.2.1) hdel

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData_originIncidentSupport_mem_of_originIncidentOwner_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (howner : doubledBoxOriginIncidentOwner n m = some ew)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m e0) :
    ew ∈ doubledBoxOriginIncidentSupport n
      (doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData
        (n := n) (v := v)
        (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
        m e0 hedge hfull hov how hvw hp).1 := by
  have hew_support : ew ∈ doubledBoxOriginIncidentSupport n m := by
    exact
      mem_doubledBoxOriginIncidentSupport.mpr
        (doubledBoxOriginIncidentOwner_spec_of_eq_some
          (n := n) (m := m) (e := ew) howner)
  rw [
    doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData_originIncidentSupport_eq_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos m e0 hedge hfull hov how hvw hp]
  exact hew_support

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData_originIncidentSupport_mem_of_originIncidentOwner_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (howner : doubledBoxOriginIncidentOwner n m = some ew)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m e0) :
    ew ∈ doubledBoxOriginIncidentSupport n
      (doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData
        (n := n) (v := v)
        (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
        m e0 hedge hfull hov how hvw hp).1 := by
  have hew_support : ew ∈ doubledBoxOriginIncidentSupport n m := by
    exact
      mem_doubledBoxOriginIncidentSupport.mpr
        (doubledBoxOriginIncidentOwner_spec_of_eq_some
          (n := n) (m := m) (e := ew) howner)
  rw [
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData_originIncidentSupport_eq_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos m e0 hedge hfull hov how hvw hp]
  exact hew_support

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData_originIncidentSupport_eq_singleton_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hsupport : doubledBoxOriginIncidentSupport n m = {ew})
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m e0) :
    doubledBoxOriginIncidentSupport n
        (doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData
          (n := n) (v := v)
          (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          m e0 hedge hfull hov how hvw hp).1 = {ew} := by
  rw [
    doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairData_originIncidentSupport_eq_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos m e0 hedge hfull hov how hvw hp,
    hsupport]

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData_originIncidentSupport_eq_singleton_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hsupport : doubledBoxOriginIncidentSupport n m = {ew})
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m e0) :
    doubledBoxOriginIncidentSupport n
        (doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData
          (n := n) (v := v)
          (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          m e0 hedge hfull hov how hvw hp).1 = {ew} := by
  rw [
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairData_originIncidentSupport_eq_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos m e0 hedge hfull hov how hvw hp,
    hsupport]

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentOwner_selectedEdgeCopies_ne_some_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (k : ℕ)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    doubledBoxOriginIncidentOwner n
        (Function.update
          (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) ≠
      some ew := by
  intro howner
  have hne : ew ≠ e0 :=
    doubledBoxOriginIncidentOwner_ne_selectedEdge_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (m :=
        Function.update
          (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k)
      hedge howner
  have hpos :
      (Function.update
          (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) ew ≠
        0 :=
    (doubledBoxOriginIncidentOwner_spec_of_eq_some
      (n := n)
      (m :=
        Function.update
          (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k)
      (e := ew) howner).2
  have hzero :
      (Function.update
          (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) ew =
        0 := by
    simp [Function.update_of_ne hne]
  exact hpos hzero

set_option linter.style.longLine false in


theorem not_doubledBoxIncrementedFullSourceActive_selectedEdgeCopies_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (k : ℕ)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    ¬ doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
        (Function.update
          (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) := by
  intro hactive
  have htouch :
      doubledBoxOriginTouchesEdgeSupport n
        (Function.update
          (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) :=
    doubledBoxIncrementedFullSourceActive_originTouchesEdgeSupport_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
      (m :=
        Function.update
          (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k)
      hedge hactive
  rcases
      doubledBoxOriginIncidentOwner_exists_of_originTouchesEdgeSupport
        (n := n)
        (m :=
          Function.update
            (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k)
        htouch with
    ⟨ew, _hew, howner, _hmew⟩
  exact
    doubledBoxOriginIncidentOwner_selectedEdgeCopies_ne_some_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew) k
      hedge howner

set_option linter.style.longLine false in


theorem doubledBoxSelectedEdgeCopiesSingletonCutoff_filter_originIncidentOwner_eq_empty_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (k : ℕ)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    (doubledBoxSelectedEdgeCopiesSingletonCutoff n e0 k).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew) =
      ∅ := by
  classical
  ext m
  constructor
  · intro hm
    rw [Finset.mem_filter] at hm
    have hm_eq :
        m =
          Function.update
            (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k := by
      simpa [doubledBoxSelectedEdgeCopiesSingletonCutoff] using hm.1
    have howner :
        doubledBoxOriginIncidentOwner n
            (Function.update
              (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) =
          some ew := by
      simpa [hm_eq] using hm.2
    exact False.elim
      (doubledBoxOriginIncidentOwner_selectedEdgeCopies_ne_some_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew) k
        hedge howner)
  · simp

set_option linter.style.longLine false in


theorem doubledBoxSelectedEdgeCopiesSingletonCutoff_filter_incrementedFullSourceActive_eq_empty_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (k : ℕ)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    (doubledBoxSelectedEdgeCopiesSingletonCutoff n e0 k).filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0) =
      ∅ := by
  classical
  ext m
  constructor
  · intro hm
    rw [Finset.mem_filter] at hm
    have hm_eq :
        m =
          Function.update
            (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k := by
      simpa [doubledBoxSelectedEdgeCopiesSingletonCutoff] using hm.1
    have hactive :
        doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          (Function.update
            (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) := by
      simpa [hm_eq] using hm.2
    exact False.elim
      (not_doubledBoxIncrementedFullSourceActive_selectedEdgeCopies_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) k hedge hactive)
  · simp

set_option linter.style.longLine false in


theorem doubledBoxSelectedEdgeCopiesSingletonCutoff_filter_updateSelectedEdgeMultiplicity_eq_empty_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (k : ℕ)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    (doubledBoxSelectedEdgeCopiesSingletonCutoff n e0 k).filter
        (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) =
      ∅ := by
  classical
  have hne : ew ≠ e0 :=
    doubledBoxOriginIncidentEdge_ne_strictSectorYPredecessorEdge3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge hew
  ext m
  constructor
  · intro hm
    rw [Finset.mem_filter] at hm
    have hm_eq :
        m =
          Function.update
            (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k := by
      simpa [doubledBoxSelectedEdgeCopiesSingletonCutoff] using hm.1
    have hzero :
        (Function.update m e0 (m e0 + 1)) ew = 0 := by
      rw [hm_eq]
      simp [Function.update_of_ne hne]
    exact False.elim (hm.2 hzero)
  · simp

set_option linter.style.longLine false in


theorem doubledBoxOriginIncident_updateSelectedEdge_multiplicity_eq_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    (Function.update m e0 (m e0 + 1)) ew = m ew := by
  have hne : ew ≠ e0 :=
    doubledBoxOriginIncidentEdge_ne_strictSectorYPredecessorEdge3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge hew
  simp [Function.update_of_ne hne]

set_option linter.style.longLine false in


theorem doubledBoxOriginIncident_updateSelectedEdge_multiplicity_ne_zero_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hmew : (Function.update m e0 (m e0 + 1)) ew ≠ 0) :
    m ew ≠ 0 := by
  simpa [
    doubledBoxOriginIncident_updateSelectedEdge_multiplicity_eq_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (m := m) hew hedge] using hmew

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_updateSelectedEdge_eq_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxOriginIncidentSupport n
        (Function.update m e0 (m e0 + 1)) =
      doubledBoxOriginIncidentSupport n m := by
  ext ew
  by_cases hew : ew ∈ doubledBoxOriginIncidentEdges n
  · have hEq :
        (Function.update m e0 (m e0 + 1)) ew = m ew :=
      doubledBoxOriginIncident_updateSelectedEdge_multiplicity_eq_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hew hedge
    simp [doubledBoxOriginIncidentSupport, hew, hEq]
  · simp [doubledBoxOriginIncidentSupport, hew]

set_option linter.style.longLine false in


theorem doubledBoxUpdateSelectedEdgeMultiplicity_filter_eq_multiplicity_filter_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    Ω.filter (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) =
      Ω.filter (fun m => m ew ≠ 0) := by
  ext m
  rw [Finset.mem_filter, Finset.mem_filter]
  have hEq :
      (Function.update m e0 (m e0 + 1)) ew = m ew :=
    doubledBoxOriginIncident_updateSelectedEdge_multiplicity_eq_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (m := m) hew hedge
  constructor
  · intro hm
    exact ⟨hm.1, by simpa [hEq] using hm.2⟩
  · intro hm
    exact ⟨hm.1, by simpa [hEq] using hm.2⟩

set_option linter.style.longLine false in


theorem doubledBoxActiveUpdateSelectedEdgeMultiplicity_filter_eq_activeMultiplicity_filter_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) =
      (Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => m ew ≠ 0) :=
  doubledBoxUpdateSelectedEdgeMultiplicity_filter_eq_multiplicity_filter_of_strictSectorYPredecessor3
    (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew) hew
    hedge
    (Ω.filter
      (doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0))

set_option linter.style.longLine false in


theorem doubledBoxUpdateSelectedEdgeMultiplicity_originTouchesEdgeSupport_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hmew : (Function.update m e0 (m e0 + 1)) ew ≠ 0) :
    doubledBoxOriginTouchesEdgeSupport n m := by
  refine ⟨ew, ?_, ?_⟩
  · exact
      doubledBoxOriginIncident_updateSelectedEdge_multiplicity_ne_zero_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hew hedge hmew
  · exact (mem_doubledBoxOriginIncidentEdges (n := n) (e := ew)).1 hew

set_option linter.style.longLine false in


theorem doubledBoxUpdateSelectedEdgeMultiplicity_originIncidentZeroCopy_exists_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hmew : (Function.update m e0 (m e0 + 1)) ew ≠ 0) :
    ∃ i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m,
      i.1 = ew ∧
        (i.2 : ℕ) = 0 ∧
        ew ≠ e0 ∧
        IsingFK.boxOrigin 3 (2 * n) ∈
          Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  have hne : ew ≠ e0 :=
    doubledBoxOriginIncidentEdge_ne_strictSectorYPredecessorEdge3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge hew
  have hmew_un :
      m ew ≠ 0 :=
    doubledBoxOriginIncident_updateSelectedEdge_multiplicity_ne_zero_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (m := m) hew hedge hmew
  let i : Sharpness.FluxEdgeCopy.Copy G m :=
    ⟨ew, ⟨0, Nat.pos_of_ne_zero hmew_un⟩⟩
  refine ⟨i, rfl, rfl, hne, ?_⟩
  have hends : Sharpness.FluxEdgeCopy.endsM G m i = ew.1 := by
    simp [Sharpness.FluxEdgeCopy.endsM, i]
  rw [hends]
  exact (mem_doubledBoxOriginIncidentEdges (n := n) (e := ew)).1 hew

set_option linter.style.longLine false in


theorem doubledBoxUpdateSelectedEdgeMultiplicity_filter_subset_originTouchesEdgeSupport_filter_of_strictSectorYPredecessor3
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (Ω.filter (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)) ⊆
      Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m) := by
  intro m hm
  rw [Finset.mem_filter] at hm ⊢
  exact
    ⟨hm.1,
      doubledBoxUpdateSelectedEdgeMultiplicity_originTouchesEdgeSupport_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hew hedge hm.2⟩

set_option linter.style.longLine false in


theorem forall_updateSelectedEdgeMultiplicityRows_of_forall_originTouchesEdgeSupportRows_strictSectorYPredecessor3
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {P : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop}
    (hP :
      ∀ m ∈ Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m),
        P m) :
    ∀ m ∈ Ω.filter
        (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
      P m := by
  intro m hm
  exact hP m <|
    doubledBoxUpdateSelectedEdgeMultiplicity_filter_subset_originTouchesEdgeSupport_filter_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hew hedge Ω hm

set_option linter.style.longLine false in


theorem doubledBoxUpdateSelectedEdgeMultiplicity_filter_sum_le_originTouchesEdgeSupport_filter_sum_of_nonneg_strictSectorYPredecessor3
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (f : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    (hf :
      ∀ m ∈ Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m),
        0 ≤ f m) :
    (∑ m ∈ Ω.filter
      (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
      f m) ≤
      ∑ m ∈ Ω.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m),
        f m := by
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (doubledBoxUpdateSelectedEdgeMultiplicity_filter_subset_originTouchesEdgeSupport_filter_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        hew hedge Ω)
      (fun m hm₂ _hm_not₁ => hf m hm₂)

set_option linter.style.longLine false in


theorem doubledBoxActiveUpdateSelectedEdgeMultiplicity_filter_subset_activeOriginTouchesEdgeSupport_filter_of_strictSectorYPredecessor3
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    ((Ω.filter
      (doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
      (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)) ⊆
      (Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginTouchesEdgeSupport n m) := by
  exact
    doubledBoxUpdateSelectedEdgeMultiplicity_filter_subset_originTouchesEdgeSupport_filter_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hew hedge
      (Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0))

set_option linter.style.longLine false in


theorem forall_activeUpdateSelectedEdgeMultiplicityRows_of_forall_activeOriginTouchesEdgeSupportRows_strictSectorYPredecessor3
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {P : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop}
    (hP :
      ∀ m ∈
        (Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginTouchesEdgeSupport n m),
        P m) :
    ∀ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
      P m := by
  intro m hm
  exact hP m <|
    doubledBoxActiveUpdateSelectedEdgeMultiplicity_filter_subset_activeOriginTouchesEdgeSupport_filter_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hew hedge Ω hm

set_option linter.style.longLine false in


theorem doubledBoxActiveUpdateSelectedEdgeMultiplicity_filter_sum_le_activeOriginTouchesEdgeSupport_filter_sum_of_nonneg_strictSectorYPredecessor3
    {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hew : ew ∈ doubledBoxOriginIncidentEdges n)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (f : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    (hf :
      ∀ m ∈
        (Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginTouchesEdgeSupport n m),
        0 ≤ f m) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
      f m) ≤
      ∑ m ∈
        (Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginTouchesEdgeSupport n m),
        f m := by
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (doubledBoxActiveUpdateSelectedEdgeMultiplicity_filter_subset_activeOriginTouchesEdgeSupport_filter_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        hew hedge Ω)
      (fun m hm₂ _hm_not₁ => hf m hm₂)

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentOwner_update_selectedEdge_eq_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    (Function.update m e0 (m e0 + 1)) ew = m ew := by
  have hne :
      ew ≠ e0 :=
      doubledBoxOriginIncidentOwner_ne_selectedEdge_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (m := m) hedge howner
  simp [Function.update_of_ne hne]

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentOwner_update_selectedEdge_ne_zero_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    (Function.update m e0 (m e0 + 1)) ew ≠ 0 := by
  have hpos :
      m ew ≠ 0 :=
    (doubledBoxOriginIncidentOwner_spec_of_eq_some
      (n := n) (m := m) (e := ew) howner).2
  simpa [
    doubledBoxOriginIncidentOwner_update_selectedEdge_eq_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (m := m) hedge howner] using hpos

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentOwner_updateSelectedEdge_originIncidentCopy_exists_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    ∃ i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)),
      i.1 = ew ∧
        IsingFK.boxOrigin 3 (2 * n) ∈
          Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1)) i := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  have hMew :
      M ew ≠ 0 := by
    simpa [G, M] using
      doubledBoxOriginIncidentOwner_update_selectedEdge_ne_zero_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge howner
  let i : Sharpness.FluxEdgeCopy.Copy G M :=
    ⟨ew, ⟨0, Nat.pos_of_ne_zero hMew⟩⟩
  refine ⟨i, rfl, ?_⟩
  have hends : Sharpness.FluxEdgeCopy.endsM G M i = ew.1 := by
    simp [Sharpness.FluxEdgeCopy.endsM, i]
  rw [hends]
  exact
    (mem_doubledBoxOriginIncidentEdges (n := n) (e := ew)).1
      (doubledBoxOriginIncidentOwner_spec_of_eq_some
        (n := n) (m := m) (e := ew) howner).1

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentOwner_updateSelectedEdge_originIncidentZeroCopy_exists_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    ∃ i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)),
      i.1 = ew ∧
        (i.2 : ℕ) = 0 ∧
        IsingFK.boxOrigin 3 (2 * n) ∈
          Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1)) i := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  have hMew :
      M ew ≠ 0 := by
    simpa [G, M] using
      doubledBoxOriginIncidentOwner_update_selectedEdge_ne_zero_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge howner
  let i : Sharpness.FluxEdgeCopy.Copy G M :=
    ⟨ew, ⟨0, Nat.pos_of_ne_zero hMew⟩⟩
  refine ⟨i, rfl, rfl, ?_⟩
  have hends : Sharpness.FluxEdgeCopy.endsM G M i = ew.1 := by
    simp [Sharpness.FluxEdgeCopy.endsM, i]
  rw [hends]
  exact
    (mem_doubledBoxOriginIncidentEdges (n := n) (e := ew)).1
      (doubledBoxOriginIncidentOwner_spec_of_eq_some
        (n := n) (m := m) (e := ew) howner).1

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_witnesses_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    ∃ i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)),
      ∃ j : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
          (Function.update m e0 (m e0 + 1)),
        i.1 = e0 ∧
          (i.2 : ℕ) = m e0 ∧
          j.1 = ew ∧
          (j.2 : ℕ) = 0 ∧
          ew ≠ e0 ∧
          i ≠ j ∧
          j ∈
            ((Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
                (Function.update m e0 (m e0 + 1)))) \ {i}) ∧
          ((Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1)))) \ {i}) ∈
            edgeCopySourceSector (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1)) ∧
          IsingFK.boxOrigin 3 (2 * n) ∈
            Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1)) j := by
  rcases
      doubledBoxIncrementedSelectedEdgeInsertedCopy_exists
        (n := n) (e0 := e0) (m := m) with
    ⟨i, hi, hiidx⟩
  rcases
      doubledBoxOriginIncidentOwner_updateSelectedEdge_originIncidentZeroCopy_exists_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge howner with
    ⟨j, hj, hjidx, hjorigin⟩
  have hne : ew ≠ e0 :=
    doubledBoxOriginIncidentOwner_ne_selectedEdge_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (m := m) hedge howner
  have hijne : i ≠ j := by
    intro hij
    have hew_eq_e0 : ew = e0 := by
      calc
        ew = j.1 := hj.symm
        _ = i.1 := by simp [hij]
        _ = e0 := hi
    exact hne hew_eq_e0
  refine
    ⟨i, j, hi, hiidx, hj, hjidx, hne, hijne, ?_, ?_, hjorigin⟩
  · rw [Finset.mem_sdiff]
    constructor
    · exact Finset.mem_univ j
    · intro hj_single
      rw [Finset.mem_singleton] at hj_single
      exact hijne hj_single.symm
  · exact
      doubledBoxIncrementedFullSourceActive_selectedEdgeDeletion_mem_switchedSourceSector_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
        hedge hactive (i := i) hi

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originOwnerContaining_switchedSourceSector_nonempty_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    ∃ j : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)),
      j.1 = ew ∧
        (j.2 : ℕ) = 0 ∧
        IsingFK.boxOrigin 3 (2 * n) ∈
          Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1)) j ∧
        (edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) j).Nonempty := by
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_witnesses_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨i, j, _hi, _hiidx, hj, hjidx, _hne, _hijne, hjmem, hK, hjorigin⟩
  exact
    ⟨j, hj, hjidx, hjorigin,
      edgeCopySourceSectorContainingCopy_nonempty_of_mem
        (G := FK.boxGraph 3 (2 * n))
        (A := doubledBoxOriginToInnerEndpointSource n v)
        (m := Function.update m e0 (m e0 + 1))
        (i := j)
        (K :=
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1)))) \ {i})
        hK hjmem⟩

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originOwnerContaining_switchedSourceSector_card_pos_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    ∃ j : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)),
      j.1 = ew ∧
        IsingFK.boxOrigin 3 (2 * n) ∈
          Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1)) j ∧
        0 <
          (edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) j).card := by
  rcases
      doubledBoxIncrementedFullSourceActive_originOwnerContaining_switchedSourceSector_nonempty_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨j, hj, _hjidx, hjorigin, hjnonempty⟩
  exact ⟨j, hj, hjorigin, Finset.Nonempty.card_pos hjnonempty⟩

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originOwnerExcludingInserted_switchedSourceSector_card_pos_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    ∃ owner : Sharpness.FluxEdgeCopy.Copy G M,
      owner.1 = ew ∧
        (owner.2 : ℕ) = 0 ∧
        IsingFK.boxOrigin 3 (2 * n) ∈ Sharpness.FluxEdgeCopy.endsM G M owner ∧
        0 <
          (edgeCopySourceSectorContainingAndExcludingCopy G
            (doubledBoxOriginToInnerEndpointSource n v) M owner
            (edgeCopyIncrementInserted G m e0)).card := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_witnesses_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨selected, owner, hselected, hselectedIdx, hownerEdge, hownerIdx,
      _hne, _hcopyNe, hownerMem, hKsource, hownerOrigin⟩
  let K : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
    (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \ {selected}
  have hselected_eq :
      selected = edgeCopyIncrementInserted G m e0 :=
    edgeCopy_eq_incrementInserted_of_edge_eq_of_index_eq G m e0
      (by simpa [G, M] using hselected)
      (by simpa [G, M] using hselectedIdx)
  have hselected_not_mem : edgeCopyIncrementInserted G m e0 ∉ K := by
    simp [K, hselected_eq]
  have hcard :
      0 <
        (edgeCopySourceSectorContainingAndExcludingCopy G
          (doubledBoxOriginToInnerEndpointSource n v) M owner
          (edgeCopyIncrementInserted G m e0)).card :=
    edgeCopySourceSectorContainingAndExcludingCopy_card_pos_of_mem
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n v) (m := M)
      (inside := owner) (outside := edgeCopyIncrementInserted G m e0)
      (K := K)
      (by simpa [G, M, K] using hKsource)
      (by simpa [G, M, K] using hownerMem)
      hselected_not_mem
  exact
    ⟨owner, by simpa [G, M] using hownerEdge,
      by simpa [G, M] using hownerIdx,
      by simpa [G, M] using hownerOrigin, hcard⟩

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_innerPairSourceInsertedExcludingOriginOwner_card_pos_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    ∃ owner : Sharpness.FluxEdgeCopy.Copy G M,
      owner.1 = ew ∧
        (owner.2 : ℕ) = 0 ∧
        IsingFK.boxOrigin 3 (2 * n) ∈ Sharpness.FluxEdgeCopy.endsM G M owner ∧
        0 <
          (edgeCopySourceSectorContainingAndExcludingCopy G
            (doubledBoxInnerPairSource n v w) M
            (edgeCopyIncrementInserted G m e0) owner).card := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  rcases
      doubledBoxIncrementedFullSourceActive_originOwnerExcludingInserted_switchedSourceSector_card_pos_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨owner, hownerEdge, hownerIdx, hownerOrigin, hpos⟩
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
  have hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G M)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa [G, M, w] using hactive
  have hsource :
      doubledBoxOriginToInnerEndpointSource n w ∆
          doubledBoxOriginToInnerEndpointSource n v =
        doubledBoxInnerPairSource n v w := by
    rw [symmDiff_comm]
    exact
      doubledBoxOriginToInnerEndpointSource_symmDiff_source_eq_innerPair
        (n := n) (v := v) (w := w) hov how hvw
  have hcard_eq :
      (edgeCopySourceSectorContainingAndExcludingCopy G
          (doubledBoxOriginToInnerEndpointSource n v) M owner
          (edgeCopyIncrementInserted G m e0)).card =
        (edgeCopySourceSectorContainingAndExcludingCopy G
          (doubledBoxInnerPairSource n v w) M
          (edgeCopyIncrementInserted G m e0) owner).card := by
    have h :=
      edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_card_eq
        (G := G) (A := doubledBoxOriginToInnerEndpointSource n v)
        (C := doubledBoxOriginToInnerEndpointSource n w) (m := M)
        (inside := owner) (outside := edgeCopyIncrementInserted G m e0)
        hfull
    rw [hsource] at h
    exact h
  have hpos_inner :
      0 <
        (edgeCopySourceSectorContainingAndExcludingCopy G
          (doubledBoxInnerPairSource n v w) M
          (edgeCopyIncrementInserted G m e0) owner).card := by
    rwa [hcard_eq] at hpos
  exact
    ⟨owner, by simpa [G, M, w] using hownerEdge,
      by simpa [G, M, w] using hownerIdx,
      by simpa [G, M, w] using hownerOrigin, hpos_inner⟩

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_innerPairSourceOwnerEdgeOutsideCurrent_card_pos_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    0 <
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
        (doubledBoxInnerPairSource n v w) M ew).card := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  rcases
      doubledBoxIncrementedFullSourceActive_innerPairSourceInsertedExcludingOriginOwner_card_pos_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨owner, hownerEdge, _hownerIdx, _hownerOrigin, hpos⟩
  have hle :
      (edgeCopySourceSectorContainingAndExcludingCopy G
          (doubledBoxInnerPairSource n v w) M
          (edgeCopyIncrementInserted G m e0) owner).card ≤
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
          (doubledBoxInnerPairSource n v w) M ew).card := by
    simpa [G, M, w] using
      edgeCopySourceSectorContaining_incrementInserted_excluding_owner_card_le_selectedEdgeCopyPairsOutsideCurrent_card_of_ownerEdge_eq
        G (doubledBoxInnerPairSource n v w) m e0 ew owner hownerEdge
  exact Nat.lt_of_lt_of_le hpos hle

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_outsideCurrentSelectedCopyPair_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let CopyM := Sharpness.FluxEdgeCopy.Copy G M
    ∃ i : CopyM, ∃ j : CopyM,
      let K : Finset CopyM := (Finset.univ : Finset CopyM) \ {i}
      let p : Sigma (fun _K : Finset CopyM => CopyM) := ⟨K, i⟩
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
          (doubledBoxOriginToInnerEndpointSource n v) M e0 ∧
        j ∈ K ∧
        i.1 = e0 ∧
        (i.2 : ℕ) = m e0 ∧
        j.1 = ew ∧
        (j.2 : ℕ) = 0 ∧
        ew ≠ e0 ∧
        i ≠ j ∧
        IsingFK.boxOrigin 3 (2 * n) ∈ Sharpness.FluxEdgeCopy.endsM G M j := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let CopyM := Sharpness.FluxEdgeCopy.Copy G M
  let A := doubledBoxOriginToInnerEndpointSource n v
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_witnesses_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨i, j, hi, hiidx, hj, hjidx, hne, hijne, hjmem, hK, hjorigin⟩
  refine ⟨i, j, ?_⟩
  let K : Finset CopyM := (Finset.univ : Finset CopyM) \ {i}
  let p : Sigma (fun _K : Finset CopyM => CopyM) := ⟨K, i⟩
  have hpbase : p ∈ edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0 := by
    rw [edgeCopySourceSectorSelectedEdgeCopyPairs_mem]
    exact ⟨by simpa [G, M, A, K, p] using hK, hi⟩
  have houtside : p.2 ∉ p.1 := by
    simp [p, K]
  have hpoutside :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M e0 := by
    exact
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
        G A M e0 p).mpr
        ⟨hpbase, houtside⟩
  exact
    ⟨hpoutside, by simpa [G, M, CopyM, K] using hjmem, hi, hiidx, hj,
      hjidx, hne, hijne, by simpa [G, M] using hjorigin⟩

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_switched_emptySourcePairWitness_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let CopyM := Sharpness.FluxEdgeCopy.Copy G M
    ∃ i : CopyM, ∃ j : CopyM,
      let K : Finset CopyM := (Finset.univ : Finset CopyM) \ {i}
      let p : Sigma (fun _K : Finset CopyM => CopyM) := ⟨K, i⟩
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
          (doubledBoxOriginToInnerEndpointSource n v) M e0 ∧
        copyDeletePreimageDecrementEraseFinset G M p.2 p.1 ∈
          edgeCopySourcePairWitnesses G
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (Function.update M p.2.1 (M p.2.1 - 1)) ∧
        Function.update M p.2.1 (M p.2.1 - 1) = m ∧
        j ∈ K ∧
        i.1 = e0 ∧
        (i.2 : ℕ) = m e0 ∧
        j.1 = ew ∧
        (j.2 : ℕ) = 0 ∧
        ew ≠ e0 ∧
        i ≠ j ∧
        IsingFK.boxOrigin 3 (2 * n) ∈ Sharpness.FluxEdgeCopy.endsM G M j := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let CopyM := Sharpness.FluxEdgeCopy.Copy G M
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_outsideCurrentSelectedCopyPair_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨i, j, hpoutside, hjmem, hi, hiidx, hj, hjidx, hne, hijne, hjorigin⟩
  let K : Finset CopyM := (Finset.univ : Finset CopyM) \ {i}
  let p : Sigma (fun _K : Finset CopyM => CopyM) := ⟨K, i⟩
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
  have hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G M)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa [G, M, w] using hactive
  have hwit :
      copyDeletePreimageDecrementEraseFinset G M p.2 p.1 ∈
        edgeCopySourcePairWitnesses G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n)))
          (Function.update M p.2.1 (M p.2.1 - 1)) := by
    simpa [G, M, p, K, w] using
      doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementWitness_mem
        (n := n) (v := v) (w := w) M e0
        (by simpa [w] using hedge) hfull hov how hvw (p := p)
        hpoutside
  have hprofile : Function.update M p.2.1 (M p.2.1 - 1) = m := by
    dsimp [p]
    rw [hi]
    exact edgeMultiplicityIncrement_decrement_eq m e0
  exact
    ⟨i, j, hpoutside, hwit, hprofile, by simpa [G, M, CopyM, K] using hjmem,
      hi, hiidx, hj, hjidx, hne, hijne, by simpa [G, M] using hjorigin⟩

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originOwner_switched_emptySourcePairData_of_strictSectorYPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    ∃ d : edgeCopySourcePairData G
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))),
      d.1 = m ∧
        edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) d =
          Sharpness.weight G β (fun _ => (1 : ℝ)) (Sharpness.ofEdgeFun G m) := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_switched_emptySourcePairWitness_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨i, _j, _hpoutside, hwit, hprofile, _hjmem, _hi, _hiidx, _hj, _hjidx,
      _hne, _hijne, _hjorigin⟩
  let K : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
    (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \ {i}
  let p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
      Sharpness.FluxEdgeCopy.Copy G M) := ⟨K, i⟩
  let d : edgeCopySourcePairData G
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    edgeCopySourcePairData_of_witness G (by
      simpa [G, M, K, p] using hwit)
  have hdprofile : d.1 = m := by
    simpa [d, G, M, K, p] using hprofile
  refine ⟨d, hdprofile, ?_⟩
  rw [edgeCopySourcePairDataWeight, hdprofile]

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_switched_emptySourceEquations_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    ∃ profile : ↥G.edgeFinset → ℕ,
      ∃ witness : Finset (Sharpness.FluxEdgeCopy.Copy G profile),
        profile = m ∧
          Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM G profile) witness =
            doubledBoxOriginToInnerEndpointSource n v ∧
            Sharpness.RandomCurrent.sources
                (Sharpness.FluxEdgeCopy.endsM G profile)
                ((Finset.univ :
                    Finset (Sharpness.FluxEdgeCopy.Copy G profile)) \
                  witness) =
              (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_switched_emptySourcePairWitness_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨i, _j, _hpoutside, hwit, hprofile, _hjmem, _hi, _hiidx, _hj, _hjidx,
      _hne, _hijne, _hjorigin⟩
  let K : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
    (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \ {i}
  let p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
      Sharpness.FluxEdgeCopy.Copy G M) := ⟨K, i⟩
  let profile : ↥G.edgeFinset → ℕ :=
    Function.update M p.2.1 (M p.2.1 - 1)
  let witness : Finset (Sharpness.FluxEdgeCopy.Copy G profile) :=
    copyDeletePreimageDecrementEraseFinset G M p.2 p.1
  have hwit' :
      witness ∈
        edgeCopySourcePairWitnesses G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) profile := by
    simpa [G, M, K, p, profile, witness] using hwit
  have hsource :=
    (edgeCopySourcePairWitnesses_mem G
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) profile witness).mp hwit'
  refine ⟨profile, witness, ?_, hsource.1, hsource.2⟩
  simpa [G, M, K, p, profile] using hprofile

open Classical in
set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_inCurrentSelectedDeletion_switched_innerPairSourceEquations_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) (Function.update m e0 (m e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)))}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    ∃ profile : ↥G.edgeFinset → ℕ,
      ∃ witness : Finset (Sharpness.FluxEdgeCopy.Copy G profile),
        profile = Function.update M p.2.1 (M p.2.1 - 1) ∧
          Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM G profile) witness =
            doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) ∧
            Sharpness.RandomCurrent.sources
                (Sharpness.FluxEdgeCopy.endsM G profile)
                ((Finset.univ :
                    Finset (Sharpness.FluxEdgeCopy.Copy G profile)) \
                  witness) =
              doubledBoxInnerPairSource n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
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
  have hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G M)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) =
        doubledBoxOriginToInnerEndpointSource n w := by
    simpa [G, M, w] using hactive
  let profile : ↥G.edgeFinset → ℕ :=
    Function.update M p.2.1 (M p.2.1 - 1)
  let witness : Finset (Sharpness.FluxEdgeCopy.Copy G profile) :=
    copyDeletePreimageDecrementEraseFinset G M p.2 p.1
  have hsrc :=
    doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourceEquations
      (n := n) (v := v) (w := w) M e0 (by simpa [w] using hedge)
      hfull hov how hvw (p := p) (by simpa [G, M] using hp)
  refine ⟨profile, witness, rfl, ?_, ?_⟩
  · simpa [profile, witness, G, M, w] using hsrc.1
  · simpa [profile, witness, G, M, w] using hsrc.2

open Classical in
set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_inCurrentSelectedDeletion_switched_innerPairSourceEquations_profile_eq_row_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) (Function.update m e0 (m e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)))}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0) :
    let G := FK.boxGraph 3 (2 * n)
    ∃ profile : ↥G.edgeFinset → ℕ,
      ∃ witness : Finset (Sharpness.FluxEdgeCopy.Copy G profile),
        profile = m ∧
          Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM G profile) witness =
            doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) ∧
            Sharpness.RandomCurrent.sources
                (Sharpness.FluxEdgeCopy.endsM G profile)
                ((Finset.univ :
                    Finset (Sharpness.FluxEdgeCopy.Copy G profile)) \
                  witness) =
              doubledBoxInnerPairSource n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  rcases
      doubledBoxIncrementedFullSourceActive_inCurrentSelectedDeletion_switched_innerPairSourceEquations_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
        hedge hactive (p := p) hp with
    ⟨profile, witness, hprofile, hleft, hright⟩
  have hdecrement :
      Function.update M p.2.1 (M p.2.1 - 1) = m := by
    simpa [G, M] using
      edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_decrement_increment_profile_eq
        (G := FK.boxGraph 3 (2 * n))
        (A := doubledBoxOriginToInnerEndpointSource n v)
        (e0 := e0) (m := m) (p := p) hp
  refine ⟨profile, witness, ?_, hleft, hright⟩
  exact hprofile.trans hdecrement

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_not_le_sameProfileDataWeight_div_six
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (d :
      edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hdprofile : d.1 = m)
    (hsector :
      (1 : ℝ) ≤
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ)) :
    ¬
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
          e0 m ≤
        (β / 6) *
          edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) d := by
  intro hpay
  have hβnonneg : 0 ≤ β := le_of_lt hβpos
  have hweight_pos :
      0 <
        edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) d :=
    edgeCopySourcePairDataWeight_pos_of_pos_on_support
      (FK.boxGraph 3 (2 * n)) hβpos (fun _ => (1 : ℝ)) d
      (by intro e _he; norm_num)
  have hweight_le_summand :
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) d ≤
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by
    have hle :=
      edgeCopySourcePairDataWeight_le_summand
        (FK.boxGraph 3 (2 * n)) β (fun _ => (1 : ℝ)) d
        (le_of_lt hweight_pos)
    simpa [hdprofile] using hle
  have hsummand_nonneg :
      0 ≤
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m :=
    edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
      (fun _ => (1 : ℝ)) (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβnonneg
      (by intro e; norm_num)
  have hsucc :
      (1 : ℝ) ≤ (((m e0 + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (m e0))
  have hweight_le_residual_factor :
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) d ≤
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m) := by
    calc
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) d ≤
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m := hweight_le_summand
      _ =
        (1 : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by ring
      _ ≤
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m) :=
        mul_le_mul_of_nonneg_right hsucc hsummand_nonneg
  have hβweight_le_residual :
      β *
          edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) d ≤
        doubledBoxResidualMomentEmptyBranchSummand β n v e0 m := by
    dsimp [doubledBoxResidualMomentEmptyBranchSummand]
    exact mul_le_mul_of_nonneg_left hweight_le_residual_factor hβnonneg
  have hresidual_nonneg :
      0 ≤ doubledBoxResidualMomentEmptyBranchSummand β n v e0 m :=
    doubledBoxResidualMomentEmptyBranchSummand_nonneg
      (n := n) (v := v) hβnonneg e0 m
  have hβweight_le_switched :
      β *
          edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) d ≤
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          w e0 m := by
    calc
      β *
          edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) d ≤
        doubledBoxResidualMomentEmptyBranchSummand β n v e0 m :=
          hβweight_le_residual
      _ =
        (1 : ℝ) * doubledBoxResidualMomentEmptyBranchSummand β n v e0 m := by
          ring
      _ ≤
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
            doubledBoxResidualMomentEmptyBranchSummand β n v e0 m :=
        mul_le_mul_of_nonneg_right hsector hresidual_nonneg
      _ =
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          w e0 m := by
        rfl
  have hbad :
      β *
          edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) d ≤
        (β / 6) *
          edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) d :=
    hβweight_le_switched.trans hpay
  nlinarith [hβpos, hweight_pos, hbad]

set_option linter.style.longLine false in


theorem
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_not_le_sameProfileSourceEquationWeight_div_six
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    {profile : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (witness :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile))
    (hprofile : profile = m)
    (hleft :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
          witness =
        doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
                  profile)) \
            witness) =
        (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hsector :
      (1 : ℝ) ≤
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ)) :
    ¬
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
          e0 m ≤
        (β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => (1 : ℝ))
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) profile) := by
  intro hpay
  let G := FK.boxGraph 3 (2 * n)
  have hwit :
      witness ∈
        edgeCopySourcePairWitnesses G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) profile := by
    rw [edgeCopySourcePairWitnesses_mem]
    exact ⟨by simpa [G] using hleft, by simpa [G] using hright⟩
  let d : edgeCopySourcePairData G
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    edgeCopySourcePairData_of_witness G hwit
  have hdprofile : d.1 = m := by
    exact (edgeCopySourcePairData_of_witness_profile G hwit).trans hprofile
  exact
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_not_le_sameProfileDataWeight_div_six
      (β := β) hβpos (n := n) (v := v) (w := w) e0 m d hdprofile
      hsector (by
        simpa [G, d] using hpay)

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_sameProfileSourceEquationRoute_not_pointwise_div_six_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m profile : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (witness :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile))
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (hprofile : profile = m)
    (hleft :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
          witness =
        doubledBoxOriginToInnerEndpointSource n v)
    (hright :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
                  profile)) \
            witness) =
        (∅ : Finset (FK.boxVerts 3 (2 * n)))) :
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    ¬
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
          e0 m ≤
        (β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => (1 : ℝ))
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) profile) := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  have hsector :
      (1 : ℝ) ≤
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) :=
    doubledBoxIncrementedFullSourceActive_one_le_switchedSourceSector_card_cast_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
      hedge hactive
  exact
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_not_le_sameProfileSourceEquationWeight_div_six
      (β := β) hβpos (n := n) (v := v) (w := w) e0 m witness
      hprofile hleft hright hsector

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originOwner_switched_emptySourcePairData_not_pointwise_div_six_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let G := FK.boxGraph 3 (2 * n)
    ∃ d : edgeCopySourcePairData G
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))),
      d.1 = m ∧
        ¬
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              w e0 m ≤
            (β / 6) *
              edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) d := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_switched_emptySourcePairData_of_strictSectorYPredecessor3
        (β := β) (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) (ew := ew) (m := m) hedge hactive howner with
    ⟨d, hdprofile, _hweight⟩
  refine ⟨d, hdprofile, ?_⟩
  have hsector :
      (1 : ℝ) ≤
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) :=
    doubledBoxIncrementedFullSourceActive_one_le_switchedSourceSector_card_cast_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
      hedge hactive
  simpa [G, w] using
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_not_le_sameProfileDataWeight_div_six
      (β := β) hβpos (n := n) (v := v) (w := w) e0 m d
      hdprofile hsector

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_switched_emptySourceEquations_not_pointwise_div_six_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let G := FK.boxGraph 3 (2 * n)
    ∃ profile : ↥G.edgeFinset → ℕ,
      ∃ witness : Finset (Sharpness.FluxEdgeCopy.Copy G profile),
        profile = m ∧
          Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM G profile) witness =
            doubledBoxOriginToInnerEndpointSource n v ∧
            Sharpness.RandomCurrent.sources
                (Sharpness.FluxEdgeCopy.endsM G profile)
                ((Finset.univ :
                    Finset (Sharpness.FluxEdgeCopy.Copy G profile)) \
                  witness) =
              (∅ : Finset (FK.boxVerts 3 (2 * n))) ∧
              ¬
                doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                    β n v w e0 m ≤
                  (β / 6) *
                    Sharpness.weight G β (fun _ => (1 : ℝ))
                      (Sharpness.ofEdgeFun G profile) := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_switched_emptySourceEquations_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨profile, witness, hprofile, hleft, hright⟩
  refine ⟨profile, witness, hprofile, hleft, hright, ?_⟩
  exact
    doubledBoxIncrementedFullSourceActive_sameProfileSourceEquationRoute_not_pointwise_div_six_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) (m := m) (profile := profile) witness hedge hactive
      hprofile hleft hright

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_not_le_sameProfileDataWeight_div_six
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (d :
      edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w))
    (hdprofile : d.1 = m)
    (hsector :
      (1 : ℝ) ≤
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ)) :
    ¬
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          w e0 m ≤
        (β / 6) *
          edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) d := by
  intro hpay
  have hβnonneg : 0 ≤ β := le_of_lt hβpos
  have hweight_pos :
      0 <
        edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) d :=
    edgeCopySourcePairDataWeight_pos_of_pos_on_support
      (FK.boxGraph 3 (2 * n)) hβpos (fun _ => (1 : ℝ)) d
      (by intro e _he; norm_num)
  have hweight_le_summand :
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) d ≤
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m := by
    have hle :=
      edgeCopySourcePairDataWeight_le_summand
        (FK.boxGraph 3 (2 * n)) β (fun _ => (1 : ℝ)) d
        (le_of_lt hweight_pos)
    simpa [hdprofile] using hle
  have hsummand_nonneg :
      0 ≤
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m :=
    edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
      (fun _ => (1 : ℝ)) (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m hβnonneg
      (by intro e; norm_num)
  have hsucc :
      (1 : ℝ) ≤ (((m e0 + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (m e0))
  have hweight_le_residual_factor :
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) d ≤
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) := by
    calc
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) d ≤
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m := hweight_le_summand
      _ =
        (1 : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m := by ring
      _ ≤
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) :=
        mul_le_mul_of_nonneg_right hsucc hsummand_nonneg
  have hβweight_le_residual :
      β *
          edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) d ≤
        doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m := by
    dsimp [doubledBoxResidualMomentInnerPairBranchSummand]
    exact mul_le_mul_of_nonneg_left hweight_le_residual_factor hβnonneg
  have hresidual_nonneg :
      0 ≤ doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m :=
    doubledBoxResidualMomentInnerPairBranchSummand_nonneg
      (n := n) (v := v) (w := w) hβnonneg e0 m
  have hβweight_le_switched :
      β *
          edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) d ≤
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          w e0 m := by
    calc
      β *
          edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) d ≤
        doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m :=
          hβweight_le_residual
      _ =
        (1 : ℝ) *
          doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m := by
          ring
      _ ≤
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
            doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m :=
        mul_le_mul_of_nonneg_right hsector hresidual_nonneg
      _ =
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          w e0 m := by
        rfl
  have hbad :
      β *
          edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) d ≤
        (β / 6) *
          edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) d :=
    hβweight_le_switched.trans hpay
  nlinarith [hβpos, hweight_pos, hbad]

set_option linter.style.longLine false in

theorem
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_not_le_sameProfileSourceEquationWeight_div_six
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    {profile : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (witness :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile))
    (hprofile : profile = m)
    (hleft :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
          witness =
        doubledBoxOriginToInnerEndpointSource n w)
    (hright :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
                  profile)) \
            witness) =
        doubledBoxInnerPairSource n v w)
    (hsector :
      (1 : ℝ) ≤
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ)) :
    ¬
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          w e0 m ≤
        (β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => (1 : ℝ))
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) profile) := by
  intro hpay
  let G := FK.boxGraph 3 (2 * n)
  have hwit :
      witness ∈
        edgeCopySourcePairWitnesses G
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) profile := by
    rw [edgeCopySourcePairWitnesses_mem]
    exact ⟨by simpa [G] using hleft, by simpa [G] using hright⟩
  let d : edgeCopySourcePairData G
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) :=
    edgeCopySourcePairData_of_witness G hwit
  have hdprofile : d.1 = m := by
    exact (edgeCopySourcePairData_of_witness_profile G hwit).trans hprofile
  exact
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_not_le_sameProfileDataWeight_div_six
      (β := β) hβpos (n := n) (v := v) (w := w) e0 m d hdprofile
      hsector (by
        simpa [G, d] using hpay)

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_sameProfileInnerPairSourceEquationRoute_not_pointwise_div_six_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m profile : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (witness :
      Finset
        (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) profile))
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (hprofile : profile = m)
    (hleft :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
          witness =
        doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
    (hright :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) profile)
          ((Finset.univ :
              Finset
                (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
                  profile)) \
            witness) =
        doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) :
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    ¬
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          w e0 m ≤
        (β / 6) *
          Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => (1 : ℝ))
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) profile) := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  have hsector :
      (1 : ℝ) ≤
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) :=
    doubledBoxIncrementedFullSourceActive_one_le_switchedSourceSector_card_cast_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
      hedge hactive
  exact
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_not_le_sameProfileSourceEquationWeight_div_six
      (β := β) hβpos (n := n) (v := v) (w := w) e0 m witness
      hprofile hleft hright hsector

set_option linter.style.longLine false in


theorem
    doubledBoxIncrementedFullSourceActive_inCurrentSelectedDeletion_switched_innerPairSourceEquations_not_pointwise_div_six_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) (Function.update m e0 (m e0 + 1))) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1)))}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0) :
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let G := FK.boxGraph 3 (2 * n)
    ∃ profile : ↥G.edgeFinset → ℕ,
      ∃ witness : Finset (Sharpness.FluxEdgeCopy.Copy G profile),
        profile = m ∧
          Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM G profile) witness =
            doubledBoxOriginToInnerEndpointSource n w ∧
            Sharpness.RandomCurrent.sources
                (Sharpness.FluxEdgeCopy.endsM G profile)
                ((Finset.univ :
                    Finset (Sharpness.FluxEdgeCopy.Copy G profile)) \
                  witness) =
              doubledBoxInnerPairSource n v w ∧
              ¬
                doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                    β n v w e0 m ≤
                  (β / 6) *
                    Sharpness.weight G β (fun _ => (1 : ℝ))
                      (Sharpness.ofEdgeFun G profile) := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  rcases
      doubledBoxIncrementedFullSourceActive_inCurrentSelectedDeletion_switched_innerPairSourceEquations_profile_eq_row_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
        hedge hactive (p := p) hp with
    ⟨profile, witness, hprofile, hleft, hright⟩
  refine ⟨profile, witness, hprofile, hleft, hright, ?_⟩
  exact
    doubledBoxIncrementedFullSourceActive_sameProfileInnerPairSourceEquationRoute_not_pointwise_div_six_of_strictSectorYPredecessor3
      (β := β) hβpos (n := n) (v := v) hvwedge hlt hypos
      (e0 := e0) (m := m) (profile := profile) witness hedge hactive
      hprofile hleft hright

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originOwner_switched_emptySourcePairData_route_of_strictSectorYPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let G := FK.boxGraph 3 (2 * n)
    let Ωowner :=
      (Ω.filter (fun m => doubledBoxIncrementedFullSourceActive n w e0 m)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)
    ∃ route :
        {m // m ∈ Ωowner} → edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))),
      Function.Injective route ∧
        (∀ x, (route x).1 = x.1) ∧
        (∀ x,
          edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) (route x) =
            Sharpness.weight G β (fun _ => (1 : ℝ))
              (Sharpness.ofEdgeFun G x.1)) := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let Ωowner :=
    (Ω.filter (fun m => doubledBoxIncrementedFullSourceActive n w e0 m)).filter
      (fun m => doubledBoxOriginIncidentOwner n m = some ew)
  have hdata :
      ∀ x : {m // m ∈ Ωowner},
        ∃ d : edgeCopySourcePairData G
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))),
          d.1 = x.1 ∧
            edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) d =
              Sharpness.weight G β (fun _ => (1 : ℝ))
                (Sharpness.ofEdgeFun G x.1) := by
    intro x
    have hxowner : doubledBoxOriginIncidentOwner n x.1 = some ew := by
      exact (Finset.mem_filter.mp x.2).2
    have hxactive : doubledBoxIncrementedFullSourceActive n w e0 x.1 := by
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp x.2).1).2
    simpa [G, w] using
      doubledBoxIncrementedFullSourceActive_originOwner_switched_emptySourcePairData_of_strictSectorYPredecessor3
        (β := β) (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) (ew := ew) (m := x.1) hedge hxactive hxowner
  choose route hprofile hweight using hdata
  refine ⟨route, ?_, hprofile, hweight⟩
  intro x y hxy
  apply Subtype.ext
  exact
    calc
      x.1 = (route x).1 := (hprofile x).symm
      _ = (route y).1 := congrArg Sigma.fst hxy
      _ = y.1 := hprofile y

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originOwner_switched_emptySourcePairData_route_ownerTag_eq_of_strictSectorYPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew fallback : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let G := FK.boxGraph 3 (2 * n)
    let Ωowner :=
      (Ω.filter (fun m => doubledBoxIncrementedFullSourceActive n w e0 m)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)
    ∃ route :
        {m // m ∈ Ωowner} → edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))),
      Function.Injective route ∧
        (∀ x, (route x).1 = x.1) ∧
        (∀ x,
          edgeCopySourcePairDataOriginIncidentOwnerTag
              (n := n)
              (A := doubledBoxOriginToInnerEndpointSource n v)
              (B := ∅) fallback (route x) = ew) ∧
        (∀ x,
          edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) (route x) =
            Sharpness.weight G β (fun _ => (1 : ℝ))
              (Sharpness.ofEdgeFun G x.1)) := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let Ωowner :=
    (Ω.filter (fun m => doubledBoxIncrementedFullSourceActive n w e0 m)).filter
      (fun m => doubledBoxOriginIncidentOwner n m = some ew)
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_switched_emptySourcePairData_route_of_strictSectorYPredecessor3
        (β := β) (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
        (ew := ew) hedge Ω with
    ⟨route, hinj, hprofile, hweight⟩
  refine ⟨route, hinj, hprofile, ?_, hweight⟩
  intro x
  have hxowner : doubledBoxOriginIncidentOwner n x.1 = some ew := by
    exact (Finset.mem_filter.mp x.2).2
  have hroute_owner : doubledBoxOriginIncidentOwner n (route x).1 = some ew := by
    rw [hprofile x]
    exact hxowner
  exact
    edgeCopySourcePairDataOriginIncidentOwnerTag_eq_of_profile_owner_eq_some
      (n := n)
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (B := ∅)
      fallback ew (route x) hroute_owner

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originIncidentSupportSingleton_switched_emptySourcePairData_route_of_strictSectorYPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let G := FK.boxGraph 3 (2 * n)
    let Ωsingle :=
      (Ω.filter (fun m => doubledBoxIncrementedFullSourceActive n w e0 m)).filter
        (fun m => doubledBoxOriginIncidentSupport n m = {ew})
    ∃ route :
        {m // m ∈ Ωsingle} → edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))),
      Function.Injective route ∧
        (∀ x, (route x).1 = x.1) ∧
        (∀ x, doubledBoxOriginIncidentSupport n (route x).1 = {ew}) ∧
        (∀ x,
          edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) (route x) =
            Sharpness.weight G β (fun _ => (1 : ℝ))
              (Sharpness.ofEdgeFun G x.1)) := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let Ωowner :=
    (Ω.filter (fun m => doubledBoxIncrementedFullSourceActive n w e0 m)).filter
      (fun m => doubledBoxOriginIncidentOwner n m = some ew)
  let Ωsingle :=
    (Ω.filter (fun m => doubledBoxIncrementedFullSourceActive n w e0 m)).filter
      (fun m => doubledBoxOriginIncidentSupport n m = {ew})
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_switched_emptySourcePairData_route_of_strictSectorYPredecessor3
        (β := β) (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
        (ew := ew) hedge Ω with
    ⟨ownerRoute, hownerRoute_inj, hownerRoute_profile,
      hownerRoute_weight⟩
  let embed : {m // m ∈ Ωsingle} → {m // m ∈ Ωowner} :=
    fun x =>
      ⟨x.1, by
        have hx := Finset.mem_filter.mp x.2
        have hxactive :
            x.1 ∈
              Ω.filter
                (fun m => doubledBoxIncrementedFullSourceActive n w e0 m) :=
          hx.1
        have hxsupport : doubledBoxOriginIncidentSupport n x.1 = {ew} :=
          hx.2
        have hxowner : doubledBoxOriginIncidentOwner n x.1 = some ew :=
          doubledBoxOriginIncidentOwner_eq_some_of_originIncidentSupport_eq_singleton
            (n := n) (m := x.1) (ew := ew) hxsupport
        exact Finset.mem_filter.mpr ⟨hxactive, hxowner⟩⟩
  let route :
      {m // m ∈ Ωsingle} → edgeCopySourcePairData G
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    fun x => ownerRoute (embed x)
  refine ⟨route, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have hembed : embed x = embed y := hownerRoute_inj hxy
    apply Subtype.ext
    exact congrArg
      (fun z : {m // m ∈ Ωowner} => z.1) hembed
  · intro x
    exact hownerRoute_profile (embed x)
  · intro x
    have hxsupport : doubledBoxOriginIncidentSupport n x.1 = {ew} :=
      (Finset.mem_filter.mp x.2).2
    rw [hownerRoute_profile (embed x)]
    exact hxsupport
  · intro x
    exact hownerRoute_weight (embed x)

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originIncidentSupportSingleton_switched_emptySourcePairData_weight_sum_le_sourcePairEmptySum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let G := FK.boxGraph 3 (2 * n)
    let Ωsingle :=
      (Ω.filter (fun m => doubledBoxIncrementedFullSourceActive n w e0 m)).filter
        (fun m => doubledBoxOriginIncidentSupport n m = {ew})
    (∑ m ∈ Ωsingle,
      Sharpness.weight G β (fun _ => (1 : ℝ)) (Sharpness.ofEdgeFun G m)) ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let Ωsingle :=
    (Ω.filter (fun m => doubledBoxIncrementedFullSourceActive n w e0 m)).filter
      (fun m => doubledBoxOriginIncidentSupport n m = {ew})
  rcases
      doubledBoxIncrementedFullSourceActive_originIncidentSupportSingleton_switched_emptySourcePairData_route_of_strictSectorYPredecessor3
        (β := β) (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
        (ew := ew) hedge Ω with
    ⟨route, hinj, _hprofile, _hsupport, hweight⟩
  have hroute :
      (∑ x ∈ Ωsingle.attach,
        edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) (route x)) ≤
        Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
    exact
      edgeCopySourcePairDataWeight_finset_sum_route_le_sourcePairSum_of_injOn
        (G := G) hβ (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) Ωsingle.attach route
        (by
          intro a _ha b _hb hroute_eq
          exact hinj hroute_eq)
  calc
    (∑ m ∈ Ωsingle,
      Sharpness.weight G β (fun _ => (1 : ℝ)) (Sharpness.ofEdgeFun G m)) =
        ∑ x ∈ Ωsingle.attach,
          Sharpness.weight G β (fun _ => (1 : ℝ))
            (Sharpness.ofEdgeFun G x.1) := by
      exact
        (Finset.sum_attach Ωsingle
          (fun m =>
            Sharpness.weight G β (fun _ => (1 : ℝ))
              (Sharpness.ofEdgeFun G m))).symm
    _ =
        ∑ x ∈ Ωsingle.attach,
          edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) (route x) := by
      refine Finset.sum_congr rfl ?_
      intro x _hx
      exact (hweight x).symm
    _ ≤
        Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := hroute
    _ = doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
      rfl

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originOwner_switched_emptySourcePairData_weight_sum_le_sourcePairEmptySum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let G := FK.boxGraph 3 (2 * n)
    let Ωowner :=
      (Ω.filter (fun m => doubledBoxIncrementedFullSourceActive n w e0 m)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)
    (∑ m ∈ Ωowner,
      Sharpness.weight G β (fun _ => (1 : ℝ)) (Sharpness.ofEdgeFun G m)) ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let Ωowner :=
    (Ω.filter (fun m => doubledBoxIncrementedFullSourceActive n w e0 m)).filter
      (fun m => doubledBoxOriginIncidentOwner n m = some ew)
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_switched_emptySourcePairData_route_of_strictSectorYPredecessor3
        (β := β) (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
        (ew := ew) hedge Ω with
    ⟨route, hinj, _hprofile, hweight⟩
  have hroute :
      (∑ x ∈ Ωowner.attach,
        edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) (route x)) ≤
        Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
    exact
      edgeCopySourcePairDataWeight_finset_sum_route_le_sourcePairSum_of_injOn
        (G := G) hβ (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) Ωowner.attach route
        (by
          intro a _ha b _hb hroute_eq
          exact hinj hroute_eq)
  calc
    (∑ m ∈ Ωowner,
      Sharpness.weight G β (fun _ => (1 : ℝ)) (Sharpness.ofEdgeFun G m)) =
        ∑ x ∈ Ωowner.attach,
          Sharpness.weight G β (fun _ => (1 : ℝ))
            (Sharpness.ofEdgeFun G x.1) := by
      exact
        (Finset.sum_attach Ωowner
          (fun m =>
            Sharpness.weight G β (fun _ => (1 : ℝ))
              (Sharpness.ofEdgeFun G m))).symm
    _ =
        ∑ x ∈ Ωowner.attach,
          edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) (route x) := by
      refine Finset.sum_congr rfl ?_
      intro x _hx
      exact (hweight x).symm
    _ ≤
        Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := hroute
    _ = doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
      rfl

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairsOutsideCurrent_nonempty_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1)) e0).Nonempty := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let CopyM := Sharpness.FluxEdgeCopy.Copy G M
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_outsideCurrentSelectedCopyPair_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨i, _j, hdata⟩
  let K : Finset CopyM := (Finset.univ : Finset CopyM) \ {i}
  let p : Sigma (fun _K : Finset CopyM => CopyM) := ⟨K, i⟩
  exact ⟨p, by simpa [G, M, CopyM, K, p] using hdata.1⟩

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairsOutsideCurrent_card_pos_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    0 <
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).card :=
  Finset.Nonempty.card_pos
    (doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairsOutsideCurrent_nonempty_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (m := m) hedge hactive howner)

set_option linter.style.longLine false in


theorem doubledBoxIncrementedSelectedEdgeInsertedSingleton_mem_innerPairSource_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    ({edgeCopyIncrementInserted G m e0} :
      Finset (Sharpness.FluxEdgeCopy.Copy G M)) ∈
      edgeCopySourceSector G (doubledBoxInnerPairSource n v w) M := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  rw [mem_edgeCopySourceSector]
  have hends :
      Sharpness.FluxEdgeCopy.endsM G M
          (edgeCopyIncrementInserted G m e0) =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) := by
    calc
      Sharpness.FluxEdgeCopy.endsM G M
          (edgeCopyIncrementInserted G m e0) = e0.1 := by
            exact edgeCopyIncrementInserted_ends G m e0
      _ =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) := by
            simpa [w] using hedge
  simpa [doubledBoxInnerPairSource, G, M, w] using
    randomCurrent_sources_singleton_of_ends_eq
      (Sharpness.FluxEdgeCopy.endsM G M) hends

set_option linter.style.longLine false in


theorem doubledBoxInnerPairSourceSelectedEdgeOutsideCurrent_nonempty_of_strictSectorYPredecessor3_of_selectedEdge_pos
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hmpos : 0 < m e0) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
      (doubledBoxInnerPairSource n v w) M e0).Nonempty := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
    edgeCopyIncrementInserted G m e0
  let selected : Sharpness.FluxEdgeCopy.Copy G M :=
    ⟨e0, ⟨0, by simp [M]⟩⟩
  let K : Finset (Sharpness.FluxEdgeCopy.Copy G M) := {inserted}
  let p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
      Sharpness.FluxEdgeCopy.Copy G M) := ⟨K, selected⟩
  have hK :
      K ∈ edgeCopySourceSector G (doubledBoxInnerPairSource n v w) M := by
    simpa [G, M, w, K, inserted] using
      doubledBoxIncrementedSelectedEdgeInsertedSingleton_mem_innerPairSource_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
        hedge
  have hselected_not_mem : selected ∉ K := by
    have hzero_ne : 0 ≠ m e0 := Nat.ne_of_lt hmpos
    simp [K, selected, inserted, edgeCopyIncrementInserted, hzero_ne]
  refine ⟨p, ?_⟩
  exact
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
      G (doubledBoxInnerPairSource n v w) M e0 p).mpr
      ⟨(edgeCopySourceSectorSelectedEdgeCopyPairs_mem
          (G := G) (A := doubledBoxInnerPairSource n v w)
          (m := M) (e0 := e0) (p := p)).mpr
          ⟨hK, by simp [p, selected]⟩,
        by simpa [p] using hselected_not_mem⟩

set_option linter.style.longLine false in


theorem doubledBoxInnerPairSourceSelectedEdgeOutsideCurrent_card_pos_of_strictSectorYPredecessor3_of_selectedEdge_pos
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hmpos : 0 < m e0) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    0 <
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
        (doubledBoxInnerPairSource n v w) M e0).card :=
  Finset.Nonempty.card_pos
    (doubledBoxInnerPairSourceSelectedEdgeOutsideCurrent_nonempty_of_strictSectorYPredecessor3_of_selectedEdge_pos
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
      hedge hmpos)

set_option linter.style.longLine false in


theorem doubledBoxInnerPairSourceSelectedEdgeOutsideCurrent_card_pos_of_strictSectorYPredecessor3_of_update_zero_outsideCurrent_card_lt_selectedEdgeCopyPairs_card
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (hmzero : m e0 = 0)
    (hstrict :
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card <
        (edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    0 <
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
        (doubledBoxInnerPairSource n v w) M e0).card := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  have hcont :
      0 <
        (edgeCopySourceSectorContainingCopy G
          (doubledBoxOriginToInnerEndpointSource n v) M
          (edgeCopyIncrementInserted G m e0)).card := by
    exact
      (doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_iff_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_update_zero
        (n := n) (v := v) (e0 := e0) (m := m) hmzero).mpr
        (by simpa [G, M] using hstrict)
  have hexcluding :
      0 <
        (edgeCopySourceSectorExcludingCopy G (doubledBoxInnerPairSource n v w)
          M (edgeCopyIncrementInserted G m e0)).card := by
    exact
      (doubledBoxInnerPairSource_excluding_incrementInserted_card_pos_iff_switchedSource_containing_incrementInserted_card_pos_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
        (by simpa [w] using hedge) (by simpa [w] using hactive)).mpr
        (by simpa [G, M, w] using hcont)
  exact
    (edgeCopySourceSectorExcluding_incrementInserted_card_pos_iff_selectedEdgeCopyPairsOutsideCurrent_card_pos_of_update_zero
      G (doubledBoxInnerPairSource n v w) m e0 hmzero).mp
      (by simpa [G, M, w] using hexcluding)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_selectedEdge_pos_or_zero_outsideCurrent_nonexhaustion_or_zero_outsideCurrent_exhaustion
    {n : ℕ} {v : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    (0 < m e0 ∨
        m e0 = 0 ∧
          (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1)) e0).card <
            (edgeCopySourceSectorSelectedEdgeCopyPairs
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1)) e0).card) ∨
      (m e0 = 0 ∧
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card =
          (edgeCopySourceSectorSelectedEdgeCopyPairs
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card) := by
  classical
  by_cases hmpos : 0 < m e0
  · exact Or.inl (Or.inl hmpos)
  · have hmzero : m e0 = 0 := by omega
    by_cases hstrict :
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card <
          (edgeCopySourceSectorSelectedEdgeCopyPairs
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card
    · exact Or.inl (Or.inr ⟨hmzero, hstrict⟩)
    · right
      refine ⟨hmzero, ?_⟩
      have hsplit :=
        edgeCopySourceSectorSelectedEdgeCopyPairs_branch_card_add_eq_total_card
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0
      omega

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_pair_selectedEdge_pos_or_zero_outsideCurrent_nonexhaustion_or_exists_zero_outsideCurrent_exhaustion
    {n : ℕ} {v : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 m1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    (∀ m ∈ ({m0, m1} :
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
                (Function.update m e0 (m e0 + 1)) e0).card) ∨
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
  have h0 :=
    doubledBoxOriginToInnerEndpoint_selectedEdge_pos_or_zero_outsideCurrent_nonexhaustion_or_zero_outsideCurrent_exhaustion
      (n := n) (v := v) (e0 := e0) (m := m0)
  have h1 :=
    doubledBoxOriginToInnerEndpoint_selectedEdge_pos_or_zero_outsideCurrent_nonexhaustion_or_zero_outsideCurrent_exhaustion
      (n := n) (v := v) (e0 := e0) (m := m1)
  rcases h0 with h0good | h0hard
  · rcases h1 with h1good | h1hard
    · left
      intro m hm
      have hm_cases : m = m0 ∨ m = m1 := by
        simpa using hm
      rcases hm_cases with rfl | rfl
      · exact h0good
      · exact h1good
    · right
      refine ⟨m1, ?_, h1hard.1, h1hard.2⟩
      simp
  · right
    refine ⟨m0, ?_, h0hard.1, h0hard.2⟩
    simp

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_pair_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_or_exists_zero_noPredecessor_outsideCurrent_exhaustion
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 m1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    (∀ m ∈ ({m0, m1} :
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
                  (Function.update m e0 (m e0 + 1)) e0).Nonempty))) ∨
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
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  have hrow :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        (0 < m e0 ∨
          m e0 = 0 ∧
            ((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty ∨
              ((¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                  (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
                (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
                  (FK.boxGraph 3 (2 * n))
                  (doubledBoxOriginToInnerEndpointSource n v)
                  (Function.update m e0 (m e0 + 1)) e0).Nonempty))) ∨
          (m e0 = 0 ∧
            (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
            (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
                (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n v)
                (Function.update m e0 (m e0 + 1)) e0).card =
              (edgeCopySourceSectorSelectedEdgeCopyPairs
                (FK.boxGraph 3 (2 * n))
                (doubledBoxOriginToInnerEndpointSource n v)
                (Function.update m e0 (m e0 + 1)) e0).card) := by
    intro m
    by_cases hmpos : 0 < m e0
    · exact Or.inl (Or.inl hmpos)
    · have hmzero : m e0 = 0 := by omega
      rcases
          doubledBoxOriginToInnerEndpoint_predecessorSourceSector_nonempty_or_residualInCurrent_or_outsideCurrent_exhausts_update_zero
            (n := n) (v := v) (w := w) (e0 := e0) (m := m) hmzero with
        hsource | hrest
      · exact Or.inl (Or.inr ⟨hmzero, Or.inl hsource⟩)
      · rcases hrest with hresidual | hhard
        · exact Or.inl (Or.inr ⟨hmzero, Or.inr hresidual⟩)
        · exact Or.inr ⟨hmzero, hhard.1, hhard.2⟩
  have h0 := hrow m0
  have h1 := hrow m1
  rcases h0 with h0good | h0hard
  · rcases h1 with h1good | h1hard
    · left
      intro m hm
      have hm_cases : m = m0 ∨ m = m1 := by
        simpa using hm
      rcases hm_cases with rfl | rfl
      · simpa [w] using h0good
      · simpa [w] using h1good
    · right
      refine ⟨m1, ?_, h1hard.1, ?_, h1hard.2.2⟩
      · simp
      · simpa [w] using h1hard.2.1
  · right
    refine ⟨m0, ?_, h0hard.1, ?_, h0hard.2.2⟩
    · simp
    · simpa [w] using h0hard.2.1

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_zero_noPredecessor_outsideCurrent_exhaustion_iff_zero_noPredecessor_noInCurrent
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    (m e0 = 0 ∧
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
            (Function.update m e0 (m e0 + 1)) e0).card) ↔
      (m e0 = 0 ∧
        (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            m).Nonempty) ∧
        ¬ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).Nonempty) := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let I := edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A M e0
  let O := edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M e0
  let T := edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0
  have hiff : O.card = T.card ↔ I.card = 0 := by
    simpa [G, M, A, I, O, T] using
      edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_card_eq_total_iff_inCurrent_card_eq_zero
        G A M e0
  constructor
  · intro hhard
    rcases hhard with ⟨hmzero, hnoPred, hexhaust⟩
    refine ⟨hmzero, hnoPred, ?_⟩
    intro hin
    have hzero : I.card = 0 := by
      exact hiff.mp (by simpa [G, M, A, O, T] using hexhaust)
    have hpos : 0 < I.card := Finset.Nonempty.card_pos hin
    omega
  · intro hhard
    rcases hhard with ⟨hmzero, hnoPred, hnoInCurrent⟩
    refine ⟨hmzero, hnoPred, ?_⟩
    have hzero : I.card = 0 := by
      by_contra hne
      have hpos : 0 < I.card := by omega
      exact hnoInCurrent (Finset.card_pos.mp hpos)
    exact hiff.mpr hzero

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_zero_noPredecessor_noInCurrent_iff_zero_noPredecessor_noContaining_incrementInserted
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    (m e0 = 0 ∧
        (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            m).Nonempty) ∧
        ¬ (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).Nonempty) ↔
      (m e0 = 0 ∧
        (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            m).Nonempty) ∧
        ¬ (edgeCopySourceSectorContainingCopy
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1))
            (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).Nonempty) := by
  constructor
  · intro hhard
    rcases hhard with ⟨hmzero, hnoPred, hnoInCurrent⟩
    refine ⟨hmzero, hnoPred, ?_⟩
    intro hcontaining
    exact hnoInCurrent
      ((doubledBoxOriginToInnerEndpoint_containing_incrementInserted_nonempty_iff_selectedEdgeCopyPairsInCurrent_nonempty_of_update_zero
        (n := n) (v := v) (e0 := e0) (m := m) hmzero).mp hcontaining)
  · intro hhard
    rcases hhard with ⟨hmzero, hnoPred, hnoContaining⟩
    refine ⟨hmzero, hnoPred, ?_⟩
    intro hinCurrent
    exact hnoContaining
      ((doubledBoxOriginToInnerEndpoint_containing_incrementInserted_nonempty_iff_selectedEdgeCopyPairsInCurrent_nonempty_of_update_zero
        (n := n) (v := v) (e0 := e0) (m := m) hmzero).mpr hinCurrent)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_pair_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_or_exists_zero_noPredecessor_noInCurrent
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 m1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    (∀ m ∈ ({m0, m1} :
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
                  (Function.update m e0 (m e0 + 1)) e0).Nonempty))) ∨
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
      doubledBoxOriginToInnerEndpoint_pair_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_or_exists_zero_noPredecessor_outsideCurrent_exhaustion
        (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) (m0 := m0) (m1 := m1) with
    hbranch | hhard
  · exact Or.inl hbranch
  · right
    rcases hhard with ⟨m, hm, hrow⟩
    refine ⟨m, hm, ?_⟩
    exact
      (doubledBoxOriginToInnerEndpoint_zero_noPredecessor_outsideCurrent_exhaustion_iff_zero_noPredecessor_noInCurrent
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)).mp
        hrow

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_pair_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_or_exists_zero_noPredecessor_noContaining_incrementInserted
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m0 m1 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    (∀ m ∈ ({m0, m1} :
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
                  (Function.update m e0 (m e0 + 1)) e0).Nonempty))) ∨
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
      doubledBoxOriginToInnerEndpoint_pair_selectedEdge_pos_or_zero_predecessor_or_residualInCurrent_nonempty_or_exists_zero_noPredecessor_noInCurrent
        (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) (m0 := m0) (m1 := m1) with
    hbranch | hhard
  · exact Or.inl hbranch
  · right
    rcases hhard with ⟨m, hm, hrow⟩
    refine ⟨m, hm, ?_⟩
    exact
      (doubledBoxOriginToInnerEndpoint_zero_noPredecessor_noInCurrent_iff_zero_noPredecessor_noContaining_incrementInserted
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)).mp
        hrow

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairsInCurrent_nonempty_of_strictSectorYPredecessor3_of_selectedEdge_pos
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (hmpos : 0 < m e0) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1)) e0).Nonempty := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let inserted : Sharpness.FluxEdgeCopy.Copy G M :=
    ⟨e0, ⟨m e0, by simp [M]⟩⟩
  let selected : Sharpness.FluxEdgeCopy.Copy G M :=
    ⟨e0, ⟨0, by simp [M]⟩⟩
  let K : Finset (Sharpness.FluxEdgeCopy.Copy G M) :=
    (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \ {inserted}
  let p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G M) =>
      Sharpness.FluxEdgeCopy.Copy G M) := ⟨K, selected⟩
  have hK :
      K ∈ edgeCopySourceSector G (doubledBoxOriginToInnerEndpointSource n v) M := by
    simpa [G, M, K, inserted, w] using
      doubledBoxIncrementedFullSourceActive_selectedEdgeDeletion_mem_switchedSourceSector_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
        hedge hactive (i := inserted) (by simp [inserted])
  have hselected_mem : selected ∈ K := by
    have hzero_ne : 0 ≠ m e0 := Nat.ne_of_lt hmpos
    simp [K, selected, inserted, hzero_ne]
  refine ⟨p, ?_⟩
  exact
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
      G (doubledBoxOriginToInnerEndpointSource n v) M e0 p).mpr
      ⟨(edgeCopySourceSectorSelectedEdgeCopyPairs_mem
          (G := G) (A := doubledBoxOriginToInnerEndpointSource n v)
          (m := M) (e0 := e0) (p := p)).mpr
          ⟨hK, by simp [p, selected]⟩,
        by simpa [p] using hselected_mem⟩

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairsInCurrent_card_pos_of_strictSectorYPredecessor3_of_selectedEdge_pos
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (hmpos : 0 < m e0) :
    0 <
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).card :=
  Finset.Nonempty.card_pos
    (doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairsInCurrent_nonempty_of_strictSectorYPredecessor3_of_selectedEdge_pos
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
      hedge hactive hmpos)

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairs_nonempty_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    (edgeCopySourceSectorSelectedEdgeCopyPairs
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1)) e0).Nonempty := by
  rcases
      doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairsOutsideCurrent_nonempty_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨p, hp⟩
  exact
    ⟨p,
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
        (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0 p).mp hp |>.1⟩

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairs_card_pos_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    0 <
      (edgeCopySourceSectorSelectedEdgeCopyPairs
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).card :=
  Finset.Nonempty.card_pos
    (doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairs_nonempty_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (m := m) hedge hactive howner)

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_predecessorSourceSelectedCopyPairsInCurrent_nonempty_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
      (Function.update m e0 (m e0 + 1)) e0).Nonempty := by
  classical
  exact
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_nonempty_of_fullSource_edge_pos
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
      (Function.update m e0 (m e0 + 1)) e0
      (by simpa using hactive)
      (by simp)

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_predecessorSourceSelectedCopyPairsInCurrent_card_pos_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) :
    0 <
      (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
        (Function.update m e0 (m e0 + 1)) e0).card :=
  Finset.Nonempty.card_pos
    (doubledBoxIncrementedFullSourceActive_predecessorSourceSelectedCopyPairsInCurrent_nonempty_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m) hactive)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_base_le_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m ≤
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
        β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let S :=
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
      (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1)) e0
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  have hcard_pos : 0 < S.card := by
    simpa [S, w] using
      doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairsOutsideCurrent_card_pos_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner
  have hone_le_nat : 1 ≤ S.card := Nat.succ_le_of_lt hcard_pos
  have hone_le : (1 : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hone_le_nat
  have hbase_nonneg : 0 ≤ base := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num)
  have hle : base ≤ (S.card : ℝ) * base := by
    calc
      base = (1 : ℝ) * base := by ring
      _ ≤ (S.card : ℝ) * base :=
        mul_le_mul_of_nonneg_right hone_le hbase_nonneg
  simpa [doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand,
    S, base, w] using hle

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_base_le_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
        (doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m ≤
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
        β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let S :=
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
      (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1)) e0
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m
  have hcard_pos : 0 < S.card := by
    simpa [S, w] using
      doubledBoxIncrementedFullSourceActive_switchedSelectedCopyPairsOutsideCurrent_card_pos_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner
  have hone_le_nat : 1 ≤ S.card := Nat.succ_le_of_lt hcard_pos
  have hone_le : (1 : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hone_le_nat
  have hbase_nonneg : 0 ≤ base := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num)
  have hle : base ≤ (S.card : ℝ) * base := by
    calc
      base = (1 : ℝ) * base := by ring
      _ ≤ (S.card : ℝ) * base :=
        mul_le_mul_of_nonneg_right hone_le hbase_nonneg
  simpa [
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand,
    S, base, w] using hle

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_ownerContainingExcludingCard_mul_base_le_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let A := doubledBoxOriginToInnerEndpointSource n v
    ∃ selected owner : Sharpness.FluxEdgeCopy.Copy G M,
      selected.1 = e0 ∧
        owner.1 = ew ∧
          ((edgeCopySourceSectorContainingAndExcludingCopy G A M owner
              selected).card : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) m ≤
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let S := edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M e0
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_witnesses_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨selected, owner, hselected, _hselectedIdx, hownerEdge, _hownerIdx,
      _hne, _hcopyNe, hownerMem, hKsource, _hownerOrigin⟩
  let T := edgeCopySourceSectorContainingAndExcludingCopy G A M owner selected
  refine ⟨selected, owner, hselected, hownerEdge, ?_⟩
  have hselected_not_mem :
      selected ∉
        ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \
          {selected}) := by
    simp
  have hT_mem :
      ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \
        {selected}) ∈ T := by
    exact
      (mem_edgeCopySourceSectorContainingAndExcludingCopy
        (G := G) (A := A) (m := M) (inside := owner)
        (outside := selected)).mpr
        ⟨by simpa [G, M, A, w] using hKsource,
          by simpa [G, M] using hownerMem, hselected_not_mem⟩
  have hcard_le_nat : T.card ≤ S.card := by
    simpa [T, S, G, M, A] using
      edgeCopySourceSectorContainingAndExcludingCopy_card_le_selectedEdgeCopyPairsOutsideCurrent_card
        G A M e0 owner selected (by simpa [G, M] using hselected)
  have hcard_le : (T.card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hcard_le_nat
  have hbase_nonneg : 0 ≤ base := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num)
  have hmul := mul_le_mul_of_nonneg_right hcard_le hbase_nonneg
  simpa [
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand,
    S, T, base, G, M, A, w] using hmul

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_ownerContainingExcludingCard_mul_base_le_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let A := doubledBoxOriginToInnerEndpointSource n v
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    ∃ selected owner : Sharpness.FluxEdgeCopy.Copy G M,
      selected.1 = e0 ∧
        owner.1 = ew ∧
          ((edgeCopySourceSectorContainingAndExcludingCopy G A M owner
              selected).card : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m ≤
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
              β n v w e0 m := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let S := edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G A M e0
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_witnesses_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨selected, owner, hselected, _hselectedIdx, hownerEdge, _hownerIdx,
      _hne, _hcopyNe, hownerMem, hKsource, _hownerOrigin⟩
  let T := edgeCopySourceSectorContainingAndExcludingCopy G A M owner selected
  refine ⟨selected, owner, hselected, hownerEdge, ?_⟩
  have hselected_not_mem :
      selected ∉
        ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \
          {selected}) := by
    simp
  have hT_mem :
      ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \
        {selected}) ∈ T := by
    exact
      (mem_edgeCopySourceSectorContainingAndExcludingCopy
        (G := G) (A := A) (m := M) (inside := owner)
        (outside := selected)).mpr
        ⟨by simpa [G, M, A, w] using hKsource,
          by simpa [G, M] using hownerMem, hselected_not_mem⟩
  have hcard_le_nat : T.card ≤ S.card := by
    simpa [T, S, G, M, A] using
      edgeCopySourceSectorContainingAndExcludingCopy_card_le_selectedEdgeCopyPairsOutsideCurrent_card
        G A M e0 owner selected (by simpa [G, M] using hselected)
  have hcard_le : (T.card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hcard_le_nat
  have hbase_nonneg : 0 ≤ base := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num)
  have hmul := mul_le_mul_of_nonneg_right hcard_le hbase_nonneg
  simpa [
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand,
    S, T, base, G, M, A, w] using hmul

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_ownerContainingSelectedCard_mul_base_le_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let A := doubledBoxOriginToInnerEndpointSource n v
    ∃ selected owner : Sharpness.FluxEdgeCopy.Copy G M,
      selected.1 = e0 ∧
        owner.1 = ew ∧
          ((edgeCopySourceSectorContainingBothCopies G A M owner
              selected).card : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) m ≤
            doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let S := edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A M e0
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_witnesses_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨selected, owner, hselected, _hselectedIdx, hownerEdge, _hownerIdx,
      _hne, _hcopyNe, _hownerMem, _hKsource, _hownerOrigin⟩
  let T := edgeCopySourceSectorContainingBothCopies G A M owner selected
  refine ⟨selected, owner, hselected, hownerEdge, ?_⟩
  have hcard_le_nat : T.card ≤ S.card := by
    simpa [T, S, G, M, A] using
      edgeCopySourceSectorContainingBothCopies_card_le_selectedEdgeCopyPairsInCurrent_card
        G A M e0 owner selected (by simpa [G, M] using hselected)
  have hcard_le : (T.card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hcard_le_nat
  have hbase_nonneg : 0 ≤ base := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num)
  have hmul := mul_le_mul_of_nonneg_right hcard_le hbase_nonneg
  simpa [
    doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand,
    S, T, base, G, M, A, w] using hmul

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_ownerContainingSelectedCard_mul_base_le_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let A := doubledBoxOriginToInnerEndpointSource n v
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    ∃ selected owner : Sharpness.FluxEdgeCopy.Copy G M,
      selected.1 = e0 ∧
        owner.1 = ew ∧
          ((edgeCopySourceSectorContainingBothCopies G A M owner
              selected).card : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m ≤
            doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
              β n v w e0 m := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let S := edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G A M e0
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_witnesses_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨selected, owner, hselected, _hselectedIdx, hownerEdge, _hownerIdx,
      _hne, _hcopyNe, _hownerMem, _hKsource, _hownerOrigin⟩
  let T := edgeCopySourceSectorContainingBothCopies G A M owner selected
  refine ⟨selected, owner, hselected, hownerEdge, ?_⟩
  have hcard_le_nat : T.card ≤ S.card := by
    simpa [T, S, G, M, A] using
      edgeCopySourceSectorContainingBothCopies_card_le_selectedEdgeCopyPairsInCurrent_card
        G A M e0 owner selected (by simpa [G, M] using hselected)
  have hcard_le : (T.card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hcard_le_nat
  have hbase_nonneg : 0 ≤ base := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num)
  have hmul := mul_le_mul_of_nonneg_right hcard_le hbase_nonneg
  simpa [
    doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand,
    S, T, base, G, M, A, w] using hmul

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_ownerContainingCard_mul_base_le_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let A := doubledBoxOriginToInnerEndpointSource n v
    ∃ selected owner : Sharpness.FluxEdgeCopy.Copy G M,
      selected.1 = e0 ∧
        owner.1 = ew ∧
          0 < (edgeCopySourceSectorContainingCopy G A M owner).card ∧
            ((edgeCopySourceSectorContainingCopy G A M owner).card : ℝ) *
              edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
                (∅ : Finset (FK.boxVerts 3 (2 * n))) m ≤
              doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand
                β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0 m := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let S := edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0
  let U := edgeCopySourceSectorContainingCopy G A M
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_witnesses_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨selected, owner, hselected, _hselectedIdx, hownerEdge, _hownerIdx,
      _hne, _hcopyNe, hownerMem, hKsource, _hownerOrigin⟩
  refine ⟨selected, owner, hselected, hownerEdge, ?_, ?_⟩
  · exact
      edgeCopySourceSectorContainingCopy_card_pos_of_mem
        (G := G) (A := A) (m := M) (i := owner)
        (K :=
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \
            {selected})
        (by simpa [G, M, A, w] using hKsource)
        (by simpa [G, M] using hownerMem)
  · have hcard_le_nat : (U owner).card ≤ S.card := by
      simpa [U, S, G, M, A] using
        edgeCopySourceSectorContainingCopy_card_le_selectedEdgeCopyPairs_card
          G A M e0 owner selected (by simpa [G, M] using hselected)
    have hcard_le : ((U owner).card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast hcard_le_nat
    have hbase_nonneg : 0 ≤ base := by
      exact
        edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
          (by intro e; norm_num)
    have hmul := mul_le_mul_of_nonneg_right hcard_le hbase_nonneg
    simpa [
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand,
      S, U, base, G, M, A, w] using hmul

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_ownerContainingCard_mul_base_le_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let A := doubledBoxOriginToInnerEndpointSource n v
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    ∃ selected owner : Sharpness.FluxEdgeCopy.Copy G M,
      selected.1 = e0 ∧
        owner.1 = ew ∧
          0 < (edgeCopySourceSectorContainingCopy G A M owner).card ∧
            ((edgeCopySourceSectorContainingCopy G A M owner).card : ℝ) *
              edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
                (doubledBoxInnerPairSource n v w) m ≤
              doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
                β n v w e0 m := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let S := edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0
  let U := edgeCopySourceSectorContainingCopy G A M
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_witnesses_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨selected, owner, hselected, _hselectedIdx, hownerEdge, _hownerIdx,
      _hne, _hcopyNe, hownerMem, hKsource, _hownerOrigin⟩
  refine ⟨selected, owner, hselected, hownerEdge, ?_, ?_⟩
  · exact
      edgeCopySourceSectorContainingCopy_card_pos_of_mem
        (G := G) (A := A) (m := M) (i := owner)
        (K :=
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \
            {selected})
        (by simpa [G, M, A, w] using hKsource)
        (by simpa [G, M] using hownerMem)
  · have hcard_le_nat : (U owner).card ≤ S.card := by
      simpa [U, S, G, M, A] using
        edgeCopySourceSectorContainingCopy_card_le_selectedEdgeCopyPairs_card
          G A M e0 owner selected (by simpa [G, M] using hselected)
    have hcard_le : ((U owner).card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast hcard_le_nat
    have hbase_nonneg : 0 ≤ base := by
      exact
        edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m hβ
          (by intro e; norm_num)
    have hmul := mul_le_mul_of_nonneg_right hcard_le hbase_nonneg
    simpa [
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand,
      S, U, base, G, M, A, w] using hmul

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourceSectorContainingCopy_card_emptySourcePairSummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand_of_selectedEdgeCopy
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {selected owner :
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1))}
    (hselected : selected.1 = e0) :
    β *
        (((edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) owner).card : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m) ≤
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m := by
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let U := edgeCopySourceSectorContainingCopy G A M owner
  let S := edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  have hcard_le_nat : U.card ≤ S.card := by
    simpa [U, S, G, M, A] using
      edgeCopySourceSectorContainingCopy_card_le_selectedEdgeCopyPairs_card
        G A M e0 owner selected (by simpa [G, M] using hselected)
  have hcard_le : (U.card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hcard_le_nat
  have hbase_nonneg : 0 ≤ base := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num)
  have hrow :
      (U.card : ℝ) * base ≤
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n
          v w e0 m := by
    have hmul := mul_le_mul_of_nonneg_right hcard_le hbase_nonneg
    simpa [
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand,
      S, U, base, G, M, A] using hmul
  calc
    β *
        (((edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) owner).card : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m) ≤
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β
            n v w e0 m := by
          simpa [U, base, G, M, A] using
            mul_le_mul_of_nonneg_left hrow hβ
    _ =
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
          e0 m :=
        beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_switchedSourceSectorResidualMomentEmptyBranchSummand
          β n v w e0 m

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourceSectorContainingCopy_card_innerPairSourcePairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand_of_selectedEdgeCopy
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {selected owner :
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
        (Function.update m e0 (m e0 + 1))}
    (hselected : selected.1 = e0) :
    β *
        (((edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) owner).card : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) ≤
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m := by
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let U := edgeCopySourceSectorContainingCopy G A M owner
  let S := edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0
  let base :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m
  have hcard_le_nat : U.card ≤ S.card := by
    simpa [U, S, G, M, A] using
      edgeCopySourceSectorContainingCopy_card_le_selectedEdgeCopyPairs_card
        G A M e0 owner selected (by simpa [G, M] using hselected)
  have hcard_le : (U.card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hcard_le_nat
  have hbase_nonneg : 0 ≤ base := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num)
  have hrow :
      (U.card : ℝ) * base ≤
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
          β n v w e0 m := by
    have hmul := mul_le_mul_of_nonneg_right hcard_le hbase_nonneg
    simpa [
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand,
      S, U, base, G, M, A] using hmul
  calc
    β *
        (((edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) owner).card : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) ≤
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
            β n v w e0 m := by
          simpa [U, base, G, M, A] using
            mul_le_mul_of_nonneg_left hrow hβ
    _ =
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n
          v w e0 m :=
        beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_switchedSourceSectorResidualMomentInnerPairBranchSummand
          β n v w e0 m

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourceSectorContainingCopy_card_emptySourcePairSummand_finset_sum_le_switchedSourceSectorResidualMomentEmptyBranchSummand_sum_of_selectedEdgeCopy
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (selected owner :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
          (Function.update m e0 (m e0 + 1)))
    (hselected : ∀ m ∈ Ω, (selected m).1 = e0) :
    β *
        (∑ m ∈ Ω,
          (((edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1)) (owner m)).card : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) m)) ≤
      ∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
          e0 m := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro m hm
  exact
    beta_mul_edgeCopySourceSectorContainingCopy_card_emptySourcePairSummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand_of_selectedEdgeCopy
      (β := β) hβ (n := n) (v := v) (w := w) (e0 := e0) (m := m)
      (selected := selected m) (owner := owner m) (hselected m hm)

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourceSectorContainingCopy_card_innerPairSourcePairSummand_finset_sum_le_switchedSourceSectorResidualMomentInnerPairBranchSummand_sum_of_selectedEdgeCopy
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (selected owner :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
          (Function.update m e0 (m e0 + 1)))
    (hselected : ∀ m ∈ Ω, (selected m).1 = e0) :
    β *
        (∑ m ∈ Ω,
          (((edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1)) (owner m)).card : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m)) ≤
      ∑ m ∈ Ω,
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n
          v w e0 m := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro m hm
  exact
    beta_mul_edgeCopySourceSectorContainingCopy_card_innerPairSourcePairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand_of_selectedEdgeCopy
      (β := β) hβ (n := n) (v := v) (w := w) (e0 := e0) (m := m)
      (selected := selected m) (owner := owner m) (hselected m hm)

set_option linter.style.longLine false in


theorem beta_mul_ownerContainingExcludingCard_emptySourcePairSummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let A := doubledBoxOriginToInnerEndpointSource n v
    ∃ selected owner : Sharpness.FluxEdgeCopy.Copy G M,
      selected.1 = e0 ∧
        owner.1 = ew ∧
          β *
              (((edgeCopySourceSectorContainingAndExcludingCopy G A M owner
                  selected).card : ℝ) *
                edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                  (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
                  (∅ : Finset (FK.boxVerts 3 (2 * n))) m) ≤
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_ownerContainingExcludingCard_mul_base_le_of_strictSectorYActiveOwner
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
        (ew := ew) (m := m) hedge hactive howner with
    ⟨selected, owner, hselected, hownerEdge, hrow⟩
  refine ⟨selected, owner, hselected, hownerEdge, ?_⟩
  exact
    (mul_le_mul_of_nonneg_left hrow hβ).trans
      (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand
        (β := β) (n := n) (v := v) (w := w) hβ e0 m)

set_option linter.style.longLine false in


theorem beta_mul_ownerContainingExcludingCard_innerPairSourcePairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let A := doubledBoxOriginToInnerEndpointSource n v
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    ∃ selected owner : Sharpness.FluxEdgeCopy.Copy G M,
      selected.1 = e0 ∧
        owner.1 = ew ∧
          β *
              (((edgeCopySourceSectorContainingAndExcludingCopy G A M owner
                  selected).card : ℝ) *
                edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                  (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
                  (doubledBoxInnerPairSource n v w) m) ≤
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v w e0 m := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_ownerContainingExcludingCard_mul_base_le_of_strictSectorYActiveOwner
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
        (ew := ew) (m := m) hedge hactive howner with
    ⟨selected, owner, hselected, hownerEdge, hrow⟩
  refine ⟨selected, owner, hselected, hownerEdge, ?_⟩
  exact
    (mul_le_mul_of_nonneg_left hrow hβ).trans
      (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand
        (β := β) (n := n) (v := v) (w := w) hβ e0 m)

set_option linter.style.longLine false in


theorem beta_mul_ownerContainingSelectedCard_emptySourcePairSummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let A := doubledBoxOriginToInnerEndpointSource n v
    ∃ selected owner : Sharpness.FluxEdgeCopy.Copy G M,
      selected.1 = e0 ∧
        owner.1 = ew ∧
          β *
              (((edgeCopySourceSectorContainingBothCopies G A M owner
                  selected).card : ℝ) *
                edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                  (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
                  (∅ : Finset (FK.boxVerts 3 (2 * n))) m) ≤
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases
      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_ownerContainingSelectedCard_mul_base_le_of_strictSectorYActiveOwner
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
        (ew := ew) (m := m) hedge hactive howner with
    ⟨selected, owner, hselected, hownerEdge, hrow⟩
  refine ⟨selected, owner, hselected, hownerEdge, ?_⟩
  exact
    (mul_le_mul_of_nonneg_left hrow hβ).trans
      (beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand
        (β := β) (n := n) (v := v) (w := w) hβ e0 m)

set_option linter.style.longLine false in


theorem beta_mul_ownerContainingSelectedCard_innerPairSourcePairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let A := doubledBoxOriginToInnerEndpointSource n v
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    ∃ selected owner : Sharpness.FluxEdgeCopy.Copy G M,
      selected.1 = e0 ∧
        owner.1 = ew ∧
          β *
              (((edgeCopySourceSectorContainingBothCopies G A M owner
                  selected).card : ℝ) *
                edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                  (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
                  (doubledBoxInnerPairSource n v w) m) ≤
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v w e0 m := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases
      doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_ownerContainingSelectedCard_mul_base_le_of_strictSectorYActiveOwner
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
        (ew := ew) (m := m) hedge hactive howner with
    ⟨selected, owner, hselected, hownerEdge, hrow⟩
  refine ⟨selected, owner, hselected, hownerEdge, ?_⟩
  exact
    (mul_le_mul_of_nonneg_left hrow hβ).trans
      (beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand
        (β := β) (n := n) (v := v) (w := w) hβ e0 m)

set_option linter.style.longLine false in


theorem beta_mul_ownerContainingCard_emptySourcePairSummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let A := doubledBoxOriginToInnerEndpointSource n v
    ∃ selected owner : Sharpness.FluxEdgeCopy.Copy G M,
      selected.1 = e0 ∧
        owner.1 = ew ∧
          0 < (edgeCopySourceSectorContainingCopy G A M owner).card ∧
            β *
                (((edgeCopySourceSectorContainingCopy G A M owner).card : ℝ) *
                  edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                    (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
                    (∅ : Finset (FK.boxVerts 3 (2 * n))) m) ≤
              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                e0 m := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases
      doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_ownerContainingCard_mul_base_le_of_strictSectorYActiveOwner
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
        (ew := ew) (m := m) hedge hactive howner with
    ⟨selected, owner, hselected, hownerEdge, hcard_pos, hrow⟩
  refine ⟨selected, owner, hselected, hownerEdge, hcard_pos, ?_⟩
  calc
    β *
        (((edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1)) owner).card : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m) ≤
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β
            n v w e0 m := by
          exact mul_le_mul_of_nonneg_left hrow hβ
    _ =
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
          e0 m :=
          beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_switchedSourceSectorResidualMomentEmptyBranchSummand
            β n v w e0 m

set_option linter.style.longLine false in


theorem beta_mul_ownerContainingCard_innerPairSourcePairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let A := doubledBoxOriginToInnerEndpointSource n v
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    ∃ selected owner : Sharpness.FluxEdgeCopy.Copy G M,
      selected.1 = e0 ∧
        owner.1 = ew ∧
          0 < (edgeCopySourceSectorContainingCopy G A M owner).card ∧
            β *
                (((edgeCopySourceSectorContainingCopy G A M owner).card : ℝ) *
                  edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                    (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
                    (doubledBoxInnerPairSource n v w) m) ≤
              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                β n v w e0 m := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases
      doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_ownerContainingCard_mul_base_le_of_strictSectorYActiveOwner
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
        (ew := ew) (m := m) hedge hactive howner with
    ⟨selected, owner, hselected, hownerEdge, hcard_pos, hrow⟩
  refine ⟨selected, owner, hselected, hownerEdge, hcard_pos, ?_⟩
  calc
    β *
        (((edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n v)
              (Function.update m e0 (m e0 + 1)) owner).card : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) ≤
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
            β n v w e0 m := by
          exact mul_le_mul_of_nonneg_left hrow hβ
    _ =
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          w e0 m :=
          beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_switchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v w e0 m

set_option linter.style.longLine false in


theorem doubledBoxStrictSectorYActiveOwner_commonSelectedOwnerContainingCardResidualPayments
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    let G := FK.boxGraph 3 (2 * n)
    let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
    let A := doubledBoxOriginToInnerEndpointSource n v
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let emptyBase : ℝ :=
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m
    let innerBase : ℝ :=
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m
    ∃ selected owner : Sharpness.FluxEdgeCopy.Copy G M,
      selected.1 = e0 ∧
        owner.1 = ew ∧
          (edgeCopySourceSectorContainingBothCopies G A M owner selected).card +
              (edgeCopySourceSectorContainingAndExcludingCopy G A M owner
                selected).card =
            (edgeCopySourceSectorContainingCopy G A M owner).card ∧
          0 < (edgeCopySourceSectorContainingCopy G A M owner).card ∧
          β *
              (((edgeCopySourceSectorContainingCopy G A M owner).card : ℝ) *
                emptyBase) ≤
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              w e0 m ∧
          β *
              (((edgeCopySourceSectorContainingCopy G A M owner).card : ℝ) *
                innerBase) ≤
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v w e0 m := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥G.edgeFinset → ℕ := Function.update m e0 (m e0 + 1)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let emptyBase : ℝ :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  let innerBase : ℝ :=
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m
  let S := edgeCopySourceSectorSelectedEdgeCopyPairs G A M e0
  rcases
      doubledBoxIncrementedFullSourceActive_originOwner_selectedDeletion_witnesses_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge hactive howner with
    ⟨selected, owner, hselected, _hselectedIdx, hownerEdge, _hownerIdx,
      _hne, _hcopyNe, hownerMem, hKsource, _hownerOrigin⟩
  let U := edgeCopySourceSectorContainingCopy G A M owner
  refine
    ⟨selected, owner, hselected, hownerEdge, ?_, ?_, ?_, ?_⟩
  · simpa [G, M, A] using
      edgeCopySourceSectorContainingCopy_branch_card_add_eq G A M owner
        selected
  · exact
      edgeCopySourceSectorContainingCopy_card_pos_of_mem
        (G := G) (A := A) (m := M) (i := owner)
        (K :=
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G M)) \
            {selected})
        (by simpa [G, M, A, w] using hKsource)
        (by simpa [G, M] using hownerMem)
  · have hcard_le_nat : U.card ≤ S.card := by
      simpa [U, S, G, M, A] using
        edgeCopySourceSectorContainingCopy_card_le_selectedEdgeCopyPairs_card
          G A M e0 owner selected (by simpa [G, M] using hselected)
    have hcard_le : (U.card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast hcard_le_nat
    have hbase_nonneg : 0 ≤ emptyBase := by
      exact
        edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
          (by intro e; norm_num)
    have hrow :
        (U.card : ℝ) * emptyBase ≤
          doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β
            n v w e0 m := by
      have hmul := mul_le_mul_of_nonneg_right hcard_le hbase_nonneg
      simpa [
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand,
        S, U, emptyBase, G, M, A, w] using hmul
    have hres :
        β * ((U.card : ℝ) * emptyBase) ≤
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            w e0 m := by
      calc
        β * ((U.card : ℝ) * emptyBase) ≤
            β *
              doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand
                β n v w e0 m := by
              exact mul_le_mul_of_nonneg_left hrow hβ
        _ =
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n
              v w e0 m :=
              beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_switchedSourceSectorResidualMomentEmptyBranchSummand
                β n v w e0 m
    simpa [U, emptyBase, G, M, A, w] using hres
  · have hcard_le_nat : U.card ≤ S.card := by
      simpa [U, S, G, M, A] using
        edgeCopySourceSectorContainingCopy_card_le_selectedEdgeCopyPairs_card
          G A M e0 owner selected (by simpa [G, M] using hselected)
    have hcard_le : (U.card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast hcard_le_nat
    have hbase_nonneg : 0 ≤ innerBase := by
      exact
        edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m hβ
          (by intro e; norm_num)
    have hrow :
        (U.card : ℝ) * innerBase ≤
          doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
            β n v w e0 m := by
      have hmul := mul_le_mul_of_nonneg_right hcard_le hbase_nonneg
      simpa [
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand,
        S, U, innerBase, G, M, A, w] using hmul
    have hres :
        β * ((U.card : ℝ) * innerBase) ≤
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β
            n v w e0 m := by
      calc
        β * ((U.card : ℝ) * innerBase) ≤
            β *
              doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
                β n v w e0 m := by
              exact mul_le_mul_of_nonneg_left hrow hβ
        _ =
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β
              n v w e0 m :=
              beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_switchedSourceSectorResidualMomentInnerPairBranchSummand
                β n v w e0 m
    simpa [U, innerBase, G, M, A, w] using hres

set_option linter.style.longLine false in


theorem doubledBoxStrictSectorYActiveOwnerFilter_exists_commonSelectedOwnerContainingCardResidualPayments_finset_sum
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    let G := FK.boxGraph 3 (2 * n)
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let A := doubledBoxOriginToInnerEndpointSource n v
    let Ωowner :=
      (Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)
    ∃ selected owner :
      ∀ m : ↥G.edgeFinset → ℕ,
        Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)),
      (∀ m ∈ Ωowner,
        (selected m).1 = e0 ∧
          (owner m).1 = ew ∧
          (edgeCopySourceSectorContainingBothCopies G A
                (Function.update m e0 (m e0 + 1)) (owner m)
                (selected m)).card +
              (edgeCopySourceSectorContainingAndExcludingCopy G A
                (Function.update m e0 (m e0 + 1)) (owner m)
                (selected m)).card =
            (edgeCopySourceSectorContainingCopy G A
              (Function.update m e0 (m e0 + 1)) (owner m)).card ∧
          0 <
            (edgeCopySourceSectorContainingCopy G A
              (Function.update m e0 (m e0 + 1)) (owner m)).card) ∧
        β *
            (∑ m ∈ Ωowner,
              (((edgeCopySourceSectorContainingCopy G A
                  (Function.update m e0 (m e0 + 1)) (owner m)).card : ℝ) *
                edgeCopySourcePairSummand G β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n v)
                  (∅ : Finset (FK.boxVerts 3 (2 * n))) m)) ≤
          ∑ m ∈ Ωowner,
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n
              v w e0 m ∧
        β *
            (∑ m ∈ Ωowner,
              (((edgeCopySourceSectorContainingCopy G A
                  (Function.update m e0 (m e0 + 1)) (owner m)).card : ℝ) *
                edgeCopySourcePairSummand G β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n w)
                  (doubledBoxInnerPairSource n v w) m)) ≤
          ∑ m ∈ Ωowner,
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v w e0 m := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let A := doubledBoxOriginToInnerEndpointSource n v
  let Ωowner :
      Finset (↥G.edgeFinset → ℕ) :=
    (Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
      (fun m => doubledBoxOriginIncidentOwner n m = some ew)
  have hwit :
      ∀ m ∈ Ωowner,
        ∃ selected owner :
          Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)),
          selected.1 = e0 ∧
            owner.1 = ew ∧
            (edgeCopySourceSectorContainingBothCopies G A
                  (Function.update m e0 (m e0 + 1)) owner selected).card +
                (edgeCopySourceSectorContainingAndExcludingCopy G A
                  (Function.update m e0 (m e0 + 1)) owner selected).card =
              (edgeCopySourceSectorContainingCopy G A
                (Function.update m e0 (m e0 + 1)) owner).card ∧
            0 <
              (edgeCopySourceSectorContainingCopy G A
                (Function.update m e0 (m e0 + 1)) owner).card ∧
            β *
                (((edgeCopySourceSectorContainingCopy G A
                    (Function.update m e0 (m e0 + 1)) owner).card : ℝ) *
                  edgeCopySourcePairSummand G β (fun _ => 1)
                    (doubledBoxOriginToInnerEndpointSource n v)
                    (∅ : Finset (FK.boxVerts 3 (2 * n))) m) ≤
              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                β n v w e0 m ∧
            β *
                (((edgeCopySourceSectorContainingCopy G A
                    (Function.update m e0 (m e0 + 1)) owner).card : ℝ) *
                  edgeCopySourcePairSummand G β (fun _ => 1)
                    (doubledBoxOriginToInnerEndpointSource n w)
                    (doubledBoxInnerPairSource n v w) m) ≤
              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                β n v w e0 m := by
    intro m hm
    have hm_filter := Finset.mem_filter.mp hm
    have hactive : doubledBoxIncrementedFullSourceActive n w e0 m :=
      (Finset.mem_filter.mp hm_filter.1).2
    have howner : doubledBoxOriginIncidentOwner n m = some ew := hm_filter.2
    rcases
        doubledBoxStrictSectorYActiveOwner_commonSelectedOwnerContainingCardResidualPayments
          (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
          (e0 := e0) (ew := ew) (m := m) hedge hactive howner with
      ⟨selected, owner, hselected, hownerEdge, hsplit, hpos, hempty,
        hinner⟩
    refine ⟨selected, owner, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [G] using hselected
    · simpa [G] using hownerEdge
    · simpa [G, A] using hsplit
    · simpa [G, A] using hpos
    · simpa [G, A, w] using hempty
    · simpa [G, A, w] using hinner
  let selected :
      ∀ m : ↥G.edgeFinset → ℕ,
        Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)) :=
    fun m =>
      if hm : m ∈ Ωowner then
        Classical.choose (hwit m hm)
      else
        edgeCopyIncrementInserted G m e0
  let owner :
      ∀ m : ↥G.edgeFinset → ℕ,
        Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)) :=
    fun m =>
      if hm : m ∈ Ωowner then
        Classical.choose (Classical.choose_spec (hwit m hm))
      else
        edgeCopyIncrementInserted G m e0
  have hrow :
      ∀ m ∈ Ωowner,
        (selected m).1 = e0 ∧
          (owner m).1 = ew ∧
          (edgeCopySourceSectorContainingBothCopies G A
                (Function.update m e0 (m e0 + 1)) (owner m)
                (selected m)).card +
              (edgeCopySourceSectorContainingAndExcludingCopy G A
                (Function.update m e0 (m e0 + 1)) (owner m)
                (selected m)).card =
            (edgeCopySourceSectorContainingCopy G A
              (Function.update m e0 (m e0 + 1)) (owner m)).card ∧
          0 <
            (edgeCopySourceSectorContainingCopy G A
              (Function.update m e0 (m e0 + 1)) (owner m)).card := by
    intro m hm
    have hspec :=
      Classical.choose_spec (Classical.choose_spec (hwit m hm))
    dsimp [selected, owner]
    rw [dif_pos hm, dif_pos hm]
    exact ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1⟩
  have hselected : ∀ m ∈ Ωowner, (selected m).1 = e0 := by
    intro m hm
    exact (hrow m hm).1
  have hempty :
      β *
          (∑ m ∈ Ωowner,
            (((edgeCopySourceSectorContainingCopy G A
                (Function.update m e0 (m e0 + 1)) (owner m)).card : ℝ) *
              edgeCopySourcePairSummand G β (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n v)
                (∅ : Finset (FK.boxVerts 3 (2 * n))) m)) ≤
        ∑ m ∈ Ωowner,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            w e0 m := by
    simpa [G, A, w] using
      beta_mul_edgeCopySourceSectorContainingCopy_card_emptySourcePairSummand_finset_sum_le_switchedSourceSectorResidualMomentEmptyBranchSummand_sum_of_selectedEdgeCopy
        (β := β) hβ (n := n) (v := v) (w := w) (e0 := e0)
        Ωowner selected owner hselected
  have hinner :
      β *
          (∑ m ∈ Ωowner,
            (((edgeCopySourceSectorContainingCopy G A
                (Function.update m e0 (m e0 + 1)) (owner m)).card : ℝ) *
              edgeCopySourcePairSummand G β (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n w)
                (doubledBoxInnerPairSource n v w) m)) ≤
        ∑ m ∈ Ωowner,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β
            n v w e0 m := by
    simpa [G, A, w] using
      beta_mul_edgeCopySourceSectorContainingCopy_card_innerPairSourcePairSummand_finset_sum_le_switchedSourceSectorResidualMomentInnerPairBranchSummand_sum_of_selectedEdgeCopy
        (β := β) hβ (n := n) (v := v) (w := w) (e0 := e0)
        Ωowner selected owner hselected
  exact ⟨selected, owner, hrow, hempty, hinner⟩

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourcePairEmptySummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    β *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m ≤
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  have hbase :=
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_base_le_of_strictSectorYActiveOwner
      (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
      (ew := ew) (m := m) hedge hactive howner
  exact
    (mul_le_mul_of_nonneg_left hbase hβ).trans
      (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand
        (β := β) (n := n) (v := v) (w := w) hβ e0 m)

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourcePairInnerPairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand_of_strictSectorYActiveOwner
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hactive :
      doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    β *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m ≤
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  have hbase :=
    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_base_le_of_strictSectorYActiveOwner
      (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
      (ew := ew) (m := m) hedge hactive howner
  exact
    (mul_le_mul_of_nonneg_left hbase hβ).trans
      (beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand
        (β := β) (n := n) (v := v) (w := w) hβ e0 m)

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourcePairEmptySummand_finset_sum_le_switchedSourceSectorResidualMomentEmptyBranchSummand_sum_of_strictSectorYActiveOwnerFilter
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    β *
                (∑ m ∈
                  Finset.filter (fun m => doubledBoxOriginIncidentOwner n m = some ew)
                    (Ω.filter
                      (doubledBoxIncrementedFullSourceActive n
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m) ≤
      ∑ m ∈
                Finset.filter (fun m => doubledBoxOriginIncidentOwner n m = some ew)
                  (Ω.filter
                    (doubledBoxIncrementedFullSourceActive n
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro m hm
  have hm_filter := Finset.mem_filter.mp hm
  have hactive := (Finset.mem_filter.mp hm_filter.1).2
  have howner := hm_filter.2
  exact
    beta_mul_edgeCopySourcePairEmptySummand_le_switchedSourceSectorResidualMomentEmptyBranchSummand_of_strictSectorYActiveOwner
      (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
      (ew := ew) (m := m) hedge hactive howner

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourcePairInnerPairSummand_finset_sum_le_switchedSourceSectorResidualMomentInnerPairBranchSummand_sum_of_strictSectorYActiveOwnerFilter
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    β *
                (∑ m ∈
                  Finset.filter (fun m => doubledBoxOriginIncidentOwner n m = some ew)
                    (Ω.filter
                      (doubledBoxIncrementedFullSourceActive n
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            (doubledBoxInnerPairSource n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) m) ≤
      ∑ m ∈
                Finset.filter (fun m => doubledBoxOriginIncidentOwner n m = some ew)
                  (Ω.filter
                    (doubledBoxIncrementedFullSourceActive n
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro m hm
  have hm_filter := Finset.mem_filter.mp hm
  have hactive := (Finset.mem_filter.mp hm_filter.1).2
  have howner := hm_filter.2
  exact
    beta_mul_edgeCopySourcePairInnerPairSummand_le_switchedSourceSectorResidualMomentInnerPairBranchSummand_of_strictSectorYActiveOwner
      (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
      (ew := ew) (m := m) hedge hactive howner

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentOwner_update_selectedEdge_originTouchesEdgeSupport_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (howner : doubledBoxOriginIncidentOwner n m = some ew) :
    doubledBoxOriginTouchesEdgeSupport n
      (Function.update m e0 (m e0 + 1)) := by
  refine ⟨ew, ?_, ?_⟩
  · exact
      doubledBoxOriginIncidentOwner_update_selectedEdge_ne_zero_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (m := m) hedge howner
  · exact
      (mem_doubledBoxOriginIncidentEdges (n := n) (e := ew)).1
        (doubledBoxOriginIncidentOwner_spec_of_eq_some
          (n := n) (m := m) (e := ew) howner).1

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_subset_updateSelectedEdge_multiplicity_filter_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    ((Ω.filter
      (doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
      (fun m => doubledBoxOriginIncidentOwner n m = some ew)) ⊆
    ((Ω.filter
      (doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
      (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)) := by
  intro m hm
  rw [Finset.mem_filter] at hm ⊢
  exact
      ⟨hm.1,
        doubledBoxOriginIncidentOwner_update_selectedEdge_ne_zero_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
          (m := m) hedge hm.2⟩

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (f : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    (hf :
      ∀ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        0 ≤ f m) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      f m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        f m := by
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_subset_updateSelectedEdge_multiplicity_filter_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        hedge Ω)
      (fun m hm₂ _hm_not₁ => hf m hm₂)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n
          v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n
            v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω
      (fun m =>
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β
            n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
      (by
        intro m _hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_nonneg
            hβ e0 m))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω
      (fun m =>
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m)
      (by
        intro m _hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_nonneg
            hβ e0 m))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω
      (fun m =>
        β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m)
      (by
        intro m _hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_nonneg
            hβ e0 m))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω
      (fun m =>
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m)
      (by
        intro m _hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_nonneg
            hβ e0 m))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          ew m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            ew m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω
      (fun m =>
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            ew m)
      (by
        intro m _hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_nonneg
            hβ e0 ew m))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω
      (fun m =>
        β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m)
      (by
        intro m _hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_nonneg
            hβ e0 m))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω
      (fun m =>
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m)
      (by
        intro m _hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_nonneg
            hβ e0 m))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          ew m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            ew m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω
      (fun m =>
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            ew m)
      (by
        intro m _hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_nonneg
            hβ e0 ew m))

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_originIncidentOwner_filter_sum_le_selectedEdgeOutside_budget_of_ownerEdge_eq_selectedEdge_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hownerEdge : ew = e0)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (outsideBudget : ℝ)
    (houtsideBudget :
      (∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m) ≤ outsideBudget) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          ew m) ≤ outsideBudget := by
  subst ew
  have hfilter :=
    beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
      (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
      (ew := e0) hedge Ω
  have hselected :
      (∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some e0)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            e0 m) ≤
        ∑ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) e0 ≠ 0)),
          β *
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
              m := by
    simpa [
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_selectedEdge_eq]
      using hfilter
  exact hselected.trans houtsideBudget

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_originIncidentOwner_filter_sum_le_selectedEdgeOutside_budget_of_ownerEdge_eq_selectedEdge_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hownerEdge : ew = e0)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (outsideBudget : ℝ)
    (houtsideBudget :
      (∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m) ≤ outsideBudget) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          ew m) ≤ outsideBudget := by
  subst ew
  have hfilter :=
    beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
      (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
      (ew := e0) hedge Ω
  have hselected :
      (∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some e0)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            e0 m) ≤
        ∑ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) e0 ≠ 0)),
          β *
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
              m := by
    simpa [
      doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_selectedEdge_eq]
      using hfilter
  exact hselected.trans houtsideBudget

set_option linter.style.longLine false in


theorem finset_sum_eq_if_mem_add_filter_ne
    {α : Type*} [DecidableEq α] (S : Finset α) (a : α) (F : α → ℝ) :
    (∑ x ∈ S, F x) =
      (if a ∈ S then F a else 0) +
        ∑ x ∈ S.filter (fun x => x ≠ a), F x := by
  classical
  by_cases ha : a ∈ S
  · have herase : S.erase a = S.filter (fun x => x ≠ a) := by
      ext x
      by_cases hxa : x = a
      · subst x
        simp
      · simp [hxa]
    calc
      (∑ x ∈ S, F x) =
          ∑ x ∈ insert a (S.erase a), F x := by
        rw [Finset.insert_erase ha]
      _ = F a + ∑ x ∈ S.erase a, F x := by
        rw [Finset.sum_insert]
        simp
      _ = (if a ∈ S then F a else 0) +
            ∑ x ∈ S.filter (fun x => x ≠ a), F x := by
        simp [ha, herase]
  · have hfilter : S.filter (fun x => x ≠ a) = S := by
      ext x
      by_cases hxS : x ∈ S
      · have hxa : x ≠ a := by
          intro h
          subst x
          exact ha hxS
        simp [hxS, hxa]
      · simp [hxS]
    simp [ha, hfilter]

set_option linter.style.longLine false in


theorem finset_sum_le_if_mem_add_filter_ne_budget
    {α : Type*} [DecidableEq α] {S : Finset α} {a : α} {F : α → ℝ}
    {selectedBudget mismatchBudget : ℝ}
    (hselected : (if a ∈ S then F a else 0) ≤ selectedBudget)
    (hmismatch :
      (∑ x ∈ S.filter (fun x => x ≠ a), F x) ≤ mismatchBudget) :
    (∑ x ∈ S, F x) ≤ selectedBudget + mismatchBudget := by
  rw [finset_sum_eq_if_mem_add_filter_ne S a F]
  exact add_le_add hselected hmismatch

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_originIncidentEdges_sum_le_selectedEdgeOutside_add_mismatch_budget_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (selectedBudget mismatchBudget : ℝ)
    (hselectedBudget :
      (∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) e0 ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m) ≤ selectedBudget)
    (hmismatchBudget :
      (∑ ew ∈ (doubledBoxOriginIncidentEdges n).filter (fun ew => ew ≠ e0),
        ∑ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
          β *
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
              ew m) ≤ mismatchBudget) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            ew m) ≤ selectedBudget + mismatchBudget := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let active := doubledBoxIncrementedFullSourceActive n w e0
  let F :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℝ :=
    fun ew =>
      ∑ m ∈ ((Ω.filter active).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
            β n v w e0 ew m
  have hselectedBudget_nonneg : 0 ≤ selectedBudget := by
    have hsum_nonneg :
        0 ≤
          (∑ m ∈
            ((Ω.filter active).filter
              (fun m => (Function.update m e0 (m e0 + 1)) e0 ≠ 0)),
            β *
              doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
                β n v w e0 m) := by
      exact Finset.sum_nonneg fun m _hm =>
        mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_nonneg
            (β := β) hβ (n := n) (v := v) (w := w) e0 m)
    exact hsum_nonneg.trans (by simpa [active, w] using hselectedBudget)
  have hselected :
      (if e0 ∈ doubledBoxOriginIncidentEdges n then F e0 else 0) ≤
        selectedBudget := by
    by_cases he0 : e0 ∈ doubledBoxOriginIncidentEdges n
    · simpa [he0, F, active, w] using
        beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_originIncidentOwner_filter_sum_le_selectedEdgeOutside_budget_of_ownerEdge_eq_selectedEdge_strictSectorYPredecessor3
          (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
          (e0 := e0) (ew := e0) hedge rfl Ω selectedBudget
          (by simpa [w] using hselectedBudget)
    · simpa [he0] using hselectedBudget_nonneg
  exact
    finset_sum_le_if_mem_add_filter_ne_budget
      (S := doubledBoxOriginIncidentEdges n) (a := e0) (F := F)
      hselected
      (by simpa [F, active, w] using hmismatchBudget)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_originIncidentEdges_sum_le_mismatch_budget_strictSectorYPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (mismatchBudget : ℝ)
    (hmismatchBudget :
      (∑ ew ∈ (doubledBoxOriginIncidentEdges n).filter (fun ew => ew ≠ e0),
        ∑ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
          β *
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
              ew m) ≤ mismatchBudget) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            ew m) ≤ mismatchBudget := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let active := doubledBoxIncrementedFullSourceActive n w e0
  let F :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℝ :=
    fun ew =>
      ∑ m ∈ ((Ω.filter active).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
            β n v w e0 ew m
  exact
    doubledBoxOriginIncidentEdges_sum_le_strictMismatch_budget_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge
      (F := F) (mismatchBudget := mismatchBudget)
      (by simpa [F, active, w] using hmismatchBudget)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_originIncidentEdges_sum_le_selectedEdgeOutside_add_mismatch_budget_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (selectedBudget mismatchBudget : ℝ)
    (hselectedBudget :
      (∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) e0 ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m) ≤ selectedBudget)
    (hmismatchBudget :
      (∑ ew ∈ (doubledBoxOriginIncidentEdges n).filter (fun ew => ew ≠ e0),
        ∑ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
          β *
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
              ew m) ≤ mismatchBudget) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            ew m) ≤ selectedBudget + mismatchBudget := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let active := doubledBoxIncrementedFullSourceActive n w e0
  let F :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℝ :=
    fun ew =>
      ∑ m ∈ ((Ω.filter active).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
            β n v w e0 ew m
  have hselectedBudget_nonneg : 0 ≤ selectedBudget := by
    have hsum_nonneg :
        0 ≤
          (∑ m ∈
            ((Ω.filter active).filter
              (fun m => (Function.update m e0 (m e0 + 1)) e0 ≠ 0)),
            β *
              doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
                β n v w e0 m) := by
      exact Finset.sum_nonneg fun m _hm =>
        mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_nonneg
            (β := β) hβ (n := n) (v := v) (w := w) e0 m)
    exact hsum_nonneg.trans (by simpa [active, w] using hselectedBudget)
  have hselected :
      (if e0 ∈ doubledBoxOriginIncidentEdges n then F e0 else 0) ≤
        selectedBudget := by
    by_cases he0 : e0 ∈ doubledBoxOriginIncidentEdges n
    · simpa [he0, F, active, w] using
        beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_originIncidentOwner_filter_sum_le_selectedEdgeOutside_budget_of_ownerEdge_eq_selectedEdge_strictSectorYPredecessor3
          (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
          (e0 := e0) (ew := e0) hedge rfl Ω selectedBudget
          (by simpa [w] using hselectedBudget)
    · simpa [he0] using hselectedBudget_nonneg
  exact
    finset_sum_le_if_mem_add_filter_ne_budget
      (S := doubledBoxOriginIncidentEdges n) (a := e0) (F := F)
      hselected
      (by simpa [F, active, w] using hmismatchBudget)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_originIncidentEdges_sum_le_mismatch_budget_strictSectorYPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (mismatchBudget : ℝ)
    (hmismatchBudget :
      (∑ ew ∈ (doubledBoxOriginIncidentEdges n).filter (fun ew => ew ≠ e0),
        ∑ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
          β *
            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
              β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
              ew m) ≤ mismatchBudget) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            ew m) ≤ mismatchBudget := by
  classical
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let active := doubledBoxIncrementedFullSourceActive n w e0
  let F :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℝ :=
    fun ew =>
      ∑ m ∈ ((Ω.filter active).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
            β n v w e0 ew m
  exact
    doubledBoxOriginIncidentEdges_sum_le_strictMismatch_budget_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge
      (F := F) (mismatchBudget := mismatchBudget)
      (by simpa [F, active, w] using hmismatchBudget)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω
      (fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
      (fun m _hm =>
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_nonneg
          hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω
      (fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
      (fun m _hm =>
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_nonneg
          hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n
        v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β
          n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew
          m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω
      (fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β
          n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew
          m)
      (fun m _hm =>
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_nonneg
          hβ e0 ew m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew
        m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew
          m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω
      (fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew
          m)
      (fun m _hm =>
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_nonneg
          hβ e0 ew m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_originIncidentEdges_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β
          n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew
          m) ≤
      ∑ ew ∈ doubledBoxOriginIncidentEdges n,
        ∑ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            ew m := by
  refine Finset.sum_le_sum ?_
  intro ew _hew
  exact
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
      (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
      (ew := ew) hedge Ω

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_originIncidentEdges_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew
          m) ≤
      ∑ ew ∈ doubledBoxOriginIncidentEdges n,
        ∑ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            ew m := by
  refine Finset.sum_le_sum ?_
  intro ew _hew
  exact
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
      (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
      (ew := ew) hedge Ω

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_residual_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          ew m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β
          n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew
          m := by
  have hpoint :
      (∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 ew m) ≤
        ∑ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0)).filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 ew m := by
    exact
      Finset.sum_le_sum (fun m _hm =>
        beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_le_switchedSourceSectorResidualMomentAtEdge
          hβ e0 ew m)
  have hfilter :
      (∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β
          n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          e0 ew m) ≤
        ∑ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 ew m :=
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
      (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
      (ew := ew) hedge Ω
  exact hpoint.trans hfilter

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_residual_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          ew m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          ew m := by
  have hpoint :
      (∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 ew m) ≤
        ∑ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0)).filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 ew m := by
    exact
      Finset.sum_le_sum (fun m _hm =>
        beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_le_switchedSourceSectorResidualMomentAtEdge
          hβ e0 ew m)
  have hfilter :
      (∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
          e0 ew m) ≤
        ∑ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            e0 ew m :=
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
      (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
      (ew := ew) hedge Ω
  exact hpoint.trans hfilter

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_originIncidentEdges_sum_le_updateSelectedEdge_multiplicity_residual_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            ew m) ≤
      ∑ ew ∈ doubledBoxOriginIncidentEdges n,
        ∑ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            ew m := by
  refine Finset.sum_le_sum ?_
  intro ew _hew
  exact
    beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummandAtEdge_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_residual_filter_sum_of_strictSectorYPredecessor3
      (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
      (ew := ew) hedge Ω

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_originIncidentEdges_sum_le_updateSelectedEdge_multiplicity_residual_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ ew ∈ doubledBoxOriginIncidentEdges n,
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            ew m) ≤
      ∑ ew ∈ doubledBoxOriginIncidentEdges n,
        ∑ m ∈
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            ew m := by
  refine Finset.sum_le_sum ?_
  intro ew _hew
  exact
    beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummandAtEdge_originIncidentOwner_filter_sum_le_updateSelectedEdge_multiplicity_residual_filter_sum_of_strictSectorYPredecessor3
      (β := β) hβ (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
      (ew := ew) hedge Ω

set_option linter.style.longLine false in


theorem forall_activeOriginIncidentOwnerRows_of_forall_updateSelectedEdgeMultiplicityRows_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {P : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop}
    (hP :
      ∀ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        P m) :
    ∀ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)),
      P m := by
  intro m hm
  exact hP m <|
    doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_subset_updateSelectedEdge_multiplicity_filter_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω hm

set_option linter.style.longLine false in


theorem forall_activeOriginIncidentSupportPatternOwnerRows_of_forall_updateSelectedEdgeMultiplicityRows_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    {P : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop}
    (hP :
      ∀ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        P m) :
    ∀ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)),
      P m := by
  intro m hm
  rw [Finset.mem_filter] at hm
  exact
    forall_activeOriginIncidentOwnerRows_of_forall_updateSelectedEdgeMultiplicityRows_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω hP m
      (by
        rw [Finset.mem_filter]
        exact ⟨hm.1, hm.2.2⟩)

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_subset_updateSelectedEdge_multiplicity_filter_of_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    ((Ω.filter
      (doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)) ⊆
    ((Ω.filter
      (doubledBoxIncrementedFullSourceActive n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
      (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)) := by
  intro m hm
  rw [Finset.mem_filter] at hm
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_subset_updateSelectedEdge_multiplicity_filter_of_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      hedge Ω
      (by
        rw [Finset.mem_filter]
        exact ⟨hm.1, hm.2.2⟩)

set_option linter.style.longLine false in


theorem doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (f : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    (hf :
      ∀ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        0 ≤ f m) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)),
      f m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        f m := by
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_subset_updateSelectedEdge_multiplicity_filter_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (S := S) hedge Ω)
      (fun m hm _hm_not => hf m hm)

set_option linter.style.longLine false in


theorem
    beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n
          v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n
            v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (S := S) hedge Ω
      (fun m =>
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β
            n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
      (by
        intro m _hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_nonneg
            hβ e0 m))

set_option linter.style.longLine false in


theorem
    beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (S := S) hedge Ω
      (fun m =>
        β *
          doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m)
      (by
        intro m _hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_nonneg
            hβ e0 m))

set_option linter.style.longLine false in


theorem
    beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (S := S) hedge Ω
      (fun m =>
        β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m)
      (by
        intro m _hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_nonneg
            hβ e0 m))

set_option linter.style.longLine false in


theorem
    beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (S := S) hedge Ω
      (fun m =>
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m)
      (by
        intro m _hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_nonneg
            hβ e0 m))

set_option linter.style.longLine false in


theorem
    beta_mul_doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (S := S) hedge Ω
      (fun m =>
        β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m)
      (by
        intro m _hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_nonneg
            hβ e0 m))

set_option linter.style.longLine false in


theorem
    beta_mul_doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)),
      β *
        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
          m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (S := S) hedge Ω
      (fun m =>
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0
            m)
      (by
        intro m _hm
        exact mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_nonneg
            hβ e0 m))

set_option linter.style.longLine false in


theorem
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)),
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (S := S) hedge Ω
      (fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
      (fun m _hm =>
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_nonneg
          hβ e0 m)

set_option linter.style.longLine false in


theorem
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)),
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (S := S) hedge Ω
      (fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
      (fun m _hm =>
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_nonneg
          hβ e0 m)

set_option linter.style.longLine false in


theorem
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)),
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β n
        v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β
          n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew
          m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (S := S) hedge Ω
      (fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge β
          n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew
          m)
      (fun m _hm =>
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_nonneg
          hβ e0 ew m)

set_option linter.style.longLine false in


theorem
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_strictSectorYPredecessor3
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    (∑ m ∈
      ((Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)),
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew
        m) ≤
      ∑ m ∈
        ((Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)),
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew
          m := by
  exact
    doubledBoxIncrementedFullSourceActive_originIncidentSupportPatternOwner_filter_sum_le_updateSelectedEdge_multiplicity_filter_sum_of_nonneg_strictSectorYPredecessor3
      (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
      (S := S) hedge Ω
      (fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
          β n v (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 ew
          m)
      (fun m _hm =>
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_nonneg
          hβ e0 ew m)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_filterSwitchedSourceSectorResidualMomentFiniteBudgetAt_expectationJSplitAt
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hbudget :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentFiniteBudgetAt
        β n)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
      β n := by
  intro v hvwedge hlt hypos
  exact
    doubledBoxOriginToInnerEndpointExpectationJ_le_of_selectedCopySplitExpectationJSplit
      hβpos
      (beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_filter_switchedSourceSectorResidualMomentBranchSummandBound_of_strictSectorYPredecessor3
        (β := β) (n := n) (v := v) hβpos hvwedge hlt hypos
        (fun e0 hedge Ω => by
          simpa [doubledBoxIncrementedFullSourceActive] using
            hbudget v hvwedge hlt hypos e0 hedge Ω))
      (by
        simpa using hJsplit v hvwedge hlt hypos)

end Exact3D
end StatMech
