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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part16
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem edgeCopySourceSectorSelectedEdgeCopyPairs_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
      Sharpness.FluxEdgeCopy.Copy G m)) :
    p ∈ edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0 ↔
      p.1 ∈ edgeCopySourceSector G A m ∧ p.2.1 = e0 := by
  classical
  rw [edgeCopySourceSectorSelectedEdgeCopyPairs, Finset.mem_sigma]
  simp [edgeCopyCopiesOfEdge_mem]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairs_connK_univ_of_edge_eq_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    {a b : V} (hab : a ≠ b) (hedge : e0.1 = s(a, b))
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy G m) =>
      Sharpness.FluxEdgeCopy.Copy G m)}
    (hp : p ∈ edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0) :
    Sharpness.RandomCurrent.connK
      (Sharpness.FluxEdgeCopy.endsM G m)
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) a b := by
  have hpbase :=
    (edgeCopySourceSectorSelectedEdgeCopyPairs_mem G A m e0 p).mp hp
  exact edgeCopy_connK_univ_of_copy_edge_eq_pair
    (G := G) (m := m) (i := p.2) hab hpbase.2 hedge

set_option linter.style.longLine false in

theorem doubledBoxOriginToInnerEndpoint_connK_univ_of_selectedEdgeCopyPair
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (A : Finset (FK.boxVerts 3 (2 * n)))
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
        (FK.boxGraph 3 (2 * n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)}
    (hp :
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairs
        (FK.boxGraph 3 (2 * n)) A m e0) :
    Sharpness.RandomCurrent.connK
      (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
      (Finset.univ :
        Finset (Sharpness.FluxEdgeCopy.Copy
          (FK.boxGraph 3 (2 * n)) m))
      (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
      (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :=
  edgeCopySourceSectorSelectedEdgeCopyPairs_connK_univ_of_edge_eq_pair
    (G := FK.boxGraph 3 (2 * n)) A m e0 hvw hedge hp

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourceSector_card_eq_of_selectedEdgeCopyPair
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n v)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
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
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairs
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m e0) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card =
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m).card := by
  have hconn :=
    doubledBoxOriginToInnerEndpoint_connK_univ_of_selectedEdgeCopyPair
      (n := n) (v := v) (w := w)
      (A := doubledBoxOriginToInnerEndpointSource n v)
      m e0 hedge hvw hp
  exact
    doubledBoxOriginToInnerEndpointSourceSector_card_eq_of_switching_conn
      (n := n) (v := v) (w := w) m hfull hov how hvw hconn

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourceSector_reverse_card_eq_of_selectedEdgeCopyPair
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
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
      p ∈ edgeCopySourceSectorSelectedEdgeCopyPairs
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m).card =
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card := by
  have hconn :=
    doubledBoxOriginToInnerEndpoint_connK_univ_of_selectedEdgeCopyPair
      (n := n) (v := v) (w := w)
      (A := doubledBoxOriginToInnerEndpointSource n w)
      m e0 hedge hvw hp
  exact
    doubledBoxOriginToInnerEndpointSourceSector_reverse_card_eq_of_switching_conn
      (n := n) (v := v) (w := w) m hfull hov how hvw hconn


theorem edgeCopySourceSectorSelectedEdgeCopyPairs_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0).card =
      (edgeCopySourceSector G A m).card * m e0 := by
  classical
  rw [edgeCopySourceSectorSelectedEdgeCopyPairs, Finset.card_sigma]
  simp [edgeCopyCopiesOfEdge_card]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairs_update_ne_card_eq_sourceSector_card_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ)
    {e0 ew : ↥G.edgeFinset} (hne : ew ≠ e0) :
    (edgeCopySourceSectorSelectedEdgeCopyPairs G A
        (Function.update m e0 (m e0 + 1)) ew).card =
      (edgeCopySourceSector G A (Function.update m e0 (m e0 + 1))).card *
        m ew := by
  rw [edgeCopySourceSectorSelectedEdgeCopyPairs_card]
  simp [Function.update_of_ne hne]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorSelectedEdgeCopyPairs_const_sum_eq_card_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (c : ℝ) :
    (∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0, c) =
      ((edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0).card : ℝ) * c := by
  rw [Finset.sum_const, nsmul_eq_mul]


theorem edgeCopySourceSectorSelectedEdgeCopyPairs_sum_weight_eq_edge_count_mul_term_of_fullSource
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A) :
    (∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0,
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m)) =
      ((m e0 : ℕ) : ℝ) * edgeCopySourcePairEmptyCollapsedTerm G β J A m := by
  classical
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  rw [edgeCopySourceSectorSelectedEdgeCopyPairs_card]
  rw [edgeCopySourcePairEmptyCollapsedTerm_eq_multiplicity_mul_weight]
  rw [edgeCopySourcePairEmptyCollapsedMultiplicity_eq_card_of_fullSource
    G A m hfull]
  norm_num [Nat.cast_mul]
  ring


theorem edgeCopySourceSectorSelectedEdgeCopyPairs_indicator_sum_weight_eq_edge_count_mul_term
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (if
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A then
        ∑ _p ∈ edgeCopySourceSectorSelectedEdgeCopyPairs G A m e0,
          Sharpness.weight G β J (Sharpness.ofEdgeFun G m)
      else
        0) =
      ((m e0 : ℕ) : ℝ) * edgeCopySourcePairEmptyCollapsedTerm G β J A m := by
  classical
  by_cases hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A
  · simpa [hfull] using
      edgeCopySourceSectorSelectedEdgeCopyPairs_sum_weight_eq_edge_count_mul_term_of_fullSource
        G β J A m e0 hfull
  · rw [edgeCopySourcePairEmptyCollapsedTerm_eq_zero_of_not_fullSource
      G β J A m hfull]
    simp [hfull]


end Exact3D
end StatMech
