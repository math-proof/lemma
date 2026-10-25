/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part8
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

theorem PeriodicPlaneEmbedding.axisSwap_bottomBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisSwap.rectBottomBoundaryVertices a b c d =
      E.rectLeftBoundaryVertices c d a b := by
  ext x
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩

theorem PeriodicPlaneEmbedding.axisSwap_topBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisSwap.rectTopBoundaryVertices a b c d =
      E.rectRightBoundaryVertices c d a b := by
  ext x
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩
  · rintro ⟨hx, y, hxy, hy⟩
    exact ⟨by simpa only [E.axisSwap_rectVertices] using hx, y, hxy, hy⟩

theorem PeriodicPlaneEmbedding.axisSwap_bottomBoundaryEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S : Set V) :
    E.axisSwap.rectSideConnectionEvent a b c d S
        (E.axisSwap.rectBottomBoundaryVertices a b c d) =
      E.rectSideConnectionEvent c d a b S
        (E.rectLeftBoundaryVertices c d a b) := by
  change P.infiniteSetConnectionWithin
    (E.axisSwap.rectVertices a b c d) S
      (E.axisSwap.rectBottomBoundaryVertices a b c d) = _
  rw [E.axisSwap_rectVertices, E.axisSwap_bottomBoundaryVertices]
  rfl

theorem PeriodicPlaneEmbedding.axisSwap_topBoundaryEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S : Set V) :
    E.axisSwap.rectSideConnectionEvent a b c d S
        (E.axisSwap.rectTopBoundaryVertices a b c d) =
      E.rectSideConnectionEvent c d a b S
        (E.rectRightBoundaryVertices c d a b) := by
  change P.infiniteSetConnectionWithin
    (E.axisSwap.rectVertices a b c d) S
      (E.axisSwap.rectTopBoundaryVertices a b c d) = _
  rw [E.axisSwap_rectVertices, E.axisSwap_topBoundaryVertices]
  rfl


theorem PeriodicPlanarDualPair.exists_common_nat_edgeArc_displacement_bound
    (D : PeriodicPlanarDualPair P Pdual) :
    ∃ B : Nat, 0 < B ∧
      (∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
        |D.primalEmbedding.coordinates
          (D.primalEmbedding.edgeArc hxy t -
            D.primalEmbedding.vertex x) i| ≤ (B : Real)) ∧
      (∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
        |D.dualEmbedding.coordinates
          (D.dualEmbedding.edgeArc hxy t -
            D.dualEmbedding.vertex x) i| ≤ (B : Real)) := by
  obtain ⟨R, hRpos, hRp, hRd⟩ :=
    D.exists_common_edgeArc_displacement_bound
  obtain ⟨B, hBR⟩ := exists_nat_gt R
  have hBpos : 0 < B := by
    by_contra hB
    have hB0 : B = 0 := Nat.eq_zero_of_not_pos hB
    subst B
    norm_num at hBR
    linarith
  refine ⟨B, hBpos, ?_, ?_⟩
  · intro x y hxy t i
    exact (hRp hxy t i).trans hBR.le
  · intro x y hxy t i
    exact (hRd hxy t i).trans hBR.le


end StatMech.FK.PeriodicPlanar
