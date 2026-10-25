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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part58
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

theorem boxParity3_adj_ne {n : ℕ} {x y : FK.boxVerts 3 n}
    (hxy : (FK.boxGraph 3 n).Adj x y) :
    boxParity3 x ≠ boxParity3 y := by
  simpa [boxParity3, FK.boxGraph] using siteParity3_adj_ne hxy

set_option linter.style.longLine false in


theorem boxParity3_adj_sub_eq_one {n : ℕ} {x y : FK.boxVerts 3 n}
    (hxy : (FK.boxGraph 3 n).Adj x y) :
    boxParity3 x - boxParity3 y = 1 := by
  simpa [boxParity3, FK.boxGraph] using siteParity3_adj_sub_eq_one hxy

set_option linter.style.longLine false in


theorem boxParity3_walk_length_cast_eq_sub {n : ℕ}
    {x y : FK.boxVerts 3 n} (p : (FK.boxGraph 3 n).Walk x y) :
    ((p.length : ℕ) : ZMod 2) = boxParity3 x - boxParity3 y := by
  induction p with
  | nil => simp
  | @cons u v w h q ih =>
      have hstep : boxParity3 u - boxParity3 v = 1 :=
        boxParity3_adj_sub_eq_one h
      calc
        (((SimpleGraph.Walk.cons h q).length : ℕ) : ZMod 2)
            = ((q.length : ℕ) : ZMod 2) + 1 := by
              simp
        _ = (boxParity3 v - boxParity3 w) + 1 := by
              rw [ih]
        _ = (boxParity3 v - boxParity3 w) +
              (boxParity3 u - boxParity3 v) := by
              rw [hstep]
        _ = boxParity3 u - boxParity3 w := by
              ring_nf

set_option linter.style.longLine false in


theorem origin_edist_ne_of_boxParity3_ne
    {n : ℕ} {x y : FK.boxVerts 3 n}
    (hpar : boxParity3 x ≠ boxParity3 y) :
    (FK.boxGraph 3 n).edist (IsingFK.boxOrigin 3 n) x ≠
      (FK.boxGraph 3 n).edist (IsingFK.boxOrigin 3 n) y := by
  intro hdist
  obtain ⟨px, hpx⟩ :=
    (boxGraph_reachable 3 n
      (IsingFK.boxOrigin 3 n) x).exists_walk_length_eq_edist
  obtain ⟨py, hpy⟩ :=
    (boxGraph_reachable 3 n
      (IsingFK.boxOrigin 3 n) y).exists_walk_length_eq_edist
  have hlenENat : (px.length : ℕ∞) = (py.length : ℕ∞) := by
    calc
      (px.length : ℕ∞) =
          (FK.boxGraph 3 n).edist (IsingFK.boxOrigin 3 n) x := hpx
      _ = (FK.boxGraph 3 n).edist (IsingFK.boxOrigin 3 n) y := hdist
      _ = (py.length : ℕ∞) := hpy.symm
  have hlen : px.length = py.length := ENat.coe_inj.mp hlenENat
  have hdiff :
      boxParity3 (IsingFK.boxOrigin 3 n) - boxParity3 x =
        boxParity3 (IsingFK.boxOrigin 3 n) - boxParity3 y := by
    calc
      boxParity3 (IsingFK.boxOrigin 3 n) - boxParity3 x =
          ((px.length : ℕ) : ZMod 2) :=
            (boxParity3_walk_length_cast_eq_sub px).symm
      _ = ((py.length : ℕ) : ZMod 2) := by
            rw [hlen]
      _ = boxParity3 (IsingFK.boxOrigin 3 n) - boxParity3 y :=
            boxParity3_walk_length_cast_eq_sub py
  have hsum := (sub_eq_sub_iff_add_eq_add.mp hdiff)
  have hpar_eq : boxParity3 x = boxParity3 y :=
    (add_left_cancel hsum).symm
  exact hpar hpar_eq

set_option linter.style.longLine false in


theorem boxParity3_strictZ_predecessor_ne
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))}) :
    boxParity3 (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
      boxParity3
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorPredecessor3 p.val p.property.1
            p.property.2)) := by
  exact
    (boxParity3_adj_ne
      (boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
        (by omega : n ≤ 2 * n) p.val p.property.1 p.property.2)).symm

set_option linter.style.longLine false in


theorem boxParity3_diagY_predecessor_ne
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) :
    boxParity3 (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
      boxParity3
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertDiagonalPredecessor3 p.val p.property.1
            p.property.2.1 p.property.2.2)) := by
  exact
    (boxParity3_adj_ne
      (boxGraph_adj_boxVertInclLE_diagonalPredecessor3
        (by omega : n ≤ 2 * n) p.val p.property.1 p.property.2.1
        p.property.2.2)).symm

set_option linter.style.longLine false in


theorem boxParity3_strictY_predecessor_ne
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))}) :
    boxParity3 (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
      boxParity3
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 p.val p.property.1
            p.property.2.1 p.property.2.2)) := by
  exact
    (boxParity3_adj_ne
      (boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
        (by omega : n ≤ 2 * n) p.val p.property.1 p.property.2.1
        p.property.2.2)).symm

set_option linter.style.longLine false in


theorem doubledBoxOriginEdist_ne_strictZ_predecessor3
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))}) :
    (FK.boxGraph 3 (2 * n)).edist
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
      (FK.boxGraph 3 (2 * n)).edist
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorPredecessor3 p.val p.property.1
            p.property.2)) :=
  origin_edist_ne_of_boxParity3_ne (boxParity3_strictZ_predecessor_ne p)

set_option linter.style.longLine false in


theorem doubledBoxOriginEdist_ne_diagY_predecessor3
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) :
    (FK.boxGraph 3 (2 * n)).edist
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
      (FK.boxGraph 3 (2 * n)).edist
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertDiagonalPredecessor3 p.val p.property.1
            p.property.2.1 p.property.2.2)) :=
  origin_edist_ne_of_boxParity3_ne (boxParity3_diagY_predecessor_ne p)

set_option linter.style.longLine false in


theorem doubledBoxOriginEdist_ne_strictY_predecessor3
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))}) :
    (FK.boxGraph 3 (2 * n)).edist
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
      (FK.boxGraph 3 (2 * n)).edist
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
          (boxVertStrictSectorYPredecessor3 p.val p.property.1
            p.property.2.1 p.property.2.2)) :=
  origin_edist_ne_of_boxParity3_ne (boxParity3_strictY_predecessor_ne p)

set_option linter.style.longLine false in


theorem doubledBoxEndpointMapObstruction_of_origin_edist_ne
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (hdist :
      (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) ≠
        (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)) :
    doubledBoxEndpointMapObstruction n v w := by
  intro φ σ hends horigin hend
  have h :=
    doubledBoxCompatibleEdgeRelabel_origin_edist_eq
      φ σ hends horigin
      (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
  rw [hend] at h
  exact hdist h.symm

set_option linter.style.longLine false in


theorem doubledBoxEndpointMapObstruction_strictZ_of_origin_edist_ne
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))})
    (hdist :
      (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
        (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorPredecessor3 p.val p.property.1
              p.property.2))) :
    doubledBoxEndpointMapObstruction n p.val
      (boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2) :=
  doubledBoxEndpointMapObstruction_of_origin_edist_ne hdist

set_option linter.style.longLine false in


theorem doubledBoxEndpointMapObstruction_diagY_of_origin_edist_ne
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))})
    (hdist :
      (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
        (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertDiagonalPredecessor3 p.val p.property.1
              p.property.2.1 p.property.2.2))) :
    doubledBoxEndpointMapObstruction n p.val
      (boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
        p.property.2.2) :=
  doubledBoxEndpointMapObstruction_of_origin_edist_ne hdist

set_option linter.style.longLine false in


theorem doubledBoxEndpointMapObstruction_strictY_of_origin_edist_ne
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))})
    (hdist :
      (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
        (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 p.val p.property.1
              p.property.2.1 p.property.2.2))) :
    doubledBoxEndpointMapObstruction n p.val
      (boxVertStrictSectorYPredecessor3 p.val p.property.1
        p.property.2.1 p.property.2.2) :=
  doubledBoxEndpointMapObstruction_of_origin_edist_ne hdist

set_option linter.style.longLine false in


theorem doubledBoxEndpointMapObstruction_strictZ
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))}) :
    doubledBoxEndpointMapObstruction n p.val
      (boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2) :=
  doubledBoxEndpointMapObstruction_strictZ_of_origin_edist_ne p
    (doubledBoxOriginEdist_ne_strictZ_predecessor3 p)

set_option linter.style.longLine false in


theorem doubledBoxEndpointMapObstruction_diagY
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) :
    doubledBoxEndpointMapObstruction n p.val
      (boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
        p.property.2.2) :=
  doubledBoxEndpointMapObstruction_diagY_of_origin_edist_ne p
    (doubledBoxOriginEdist_ne_diagY_predecessor3 p)

set_option linter.style.longLine false in


theorem doubledBoxEndpointMapObstruction_strictY
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))}) :
    doubledBoxEndpointMapObstruction n p.val
      (boxVertStrictSectorYPredecessor3 p.val p.property.1
        p.property.2.1 p.property.2.2) :=
  doubledBoxEndpointMapObstruction_strictY_of_origin_edist_ne p
    (doubledBoxOriginEdist_ne_strictY_predecessor3 p)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt.not_rowPred_strictZ_of_endpointMapObstruction
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))})
    (hobs :
      doubledBoxEndpointMapObstruction n p.val
        (boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2)) :
    ¬ T.rowPred (T.classifyStrictZ p) := by
  intro hrow
  let m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ := fun _ => 0
  exact
    hobs
      (T.vertexEquivStrictZ p hrow m)
      (T.edgeEquivStrictZ p hrow m)
      (T.endsStrictZ p hrow m)
      (T.originStrictZ p hrow m)
      (T.endpointStrictZ p hrow m)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt.not_rowPred_strictZ_of_origin_edist_ne
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))})
    (hdist :
      (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
        (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorPredecessor3 p.val p.property.1
              p.property.2))) :
    ¬ T.rowPred (T.classifyStrictZ p) :=
  T.not_rowPred_strictZ_of_endpointMapObstruction p
    (doubledBoxEndpointMapObstruction_strictZ_of_origin_edist_ne p hdist)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt.not_rowPred_diagY_of_endpointMapObstruction
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))})
    (hobs :
      doubledBoxEndpointMapObstruction n p.val
        (boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
          p.property.2.2)) :
    ¬ T.rowPred (T.classifyDiagY p) := by
  intro hrow
  let m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ := fun _ => 0
  exact
    hobs
      (T.vertexEquivDiagY p hrow m)
      (T.edgeEquivDiagY p hrow m)
      (T.endsDiagY p hrow m)
      (T.originDiagY p hrow m)
      (T.endpointDiagY p hrow m)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt.not_rowPred_diagY_of_origin_edist_ne
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))})
    (hdist :
      (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
        (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertDiagonalPredecessor3 p.val p.property.1
              p.property.2.1 p.property.2.2))) :
    ¬ T.rowPred (T.classifyDiagY p) :=
  T.not_rowPred_diagY_of_endpointMapObstruction p
    (doubledBoxEndpointMapObstruction_diagY_of_origin_edist_ne p hdist)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt.not_rowPred_strictY_of_endpointMapObstruction
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))})
    (hobs :
      doubledBoxEndpointMapObstruction n p.val
        (boxVertStrictSectorYPredecessor3 p.val p.property.1
          p.property.2.1 p.property.2.2)) :
    ¬ T.rowPred (T.classifyStrictY p) := by
  intro hrow
  let m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ := fun _ => 0
  exact
    hobs
      (T.vertexEquivStrictY p hrow m)
      (T.edgeEquivStrictY p hrow m)
      (T.endsStrictY p hrow m)
      (T.originStrictY p hrow m)
      (T.endpointStrictY p hrow m)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt.not_rowPred_strictY_of_origin_edist_ne
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))})
    (hdist :
      (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
        (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 p.val p.property.1
              p.property.2.1 p.property.2.2))) :
    ¬ T.rowPred (T.classifyStrictY p) :=
  T.not_rowPred_strictY_of_endpointMapObstruction p
    (doubledBoxEndpointMapObstruction_strictY_of_origin_edist_ne p hdist)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt.not_rowPred_strictZ
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))}) :
    ¬ T.rowPred (T.classifyStrictZ p) :=
  T.not_rowPred_strictZ_of_endpointMapObstruction p
    (doubledBoxEndpointMapObstruction_strictZ p)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt.not_rowPred_diagY
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) :
    ¬ T.rowPred (T.classifyDiagY p) :=
  T.not_rowPred_diagY_of_endpointMapObstruction p
    (doubledBoxEndpointMapObstruction_diagY p)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt.not_rowPred_strictY
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))}) :
    ¬ T.rowPred (T.classifyStrictY p) :=
  T.not_rowPred_strictY_of_endpointMapObstruction p
    (doubledBoxEndpointMapObstruction_strictY p)

end Exact3D
end StatMech
