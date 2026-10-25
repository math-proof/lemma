/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part23
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlane.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicPlaneEmbedding.rightHalfPlaneVertices
    (E : PeriodicPlaneEmbedding P) (r : ℝ) : Set V :=
  {x | r ≤ E.vertexCoord x 0}


def PeriodicPlaneEmbedding.rightHalfPlaneBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (r : ℝ) : Set V :=
  {x | x ∈ E.rightHalfPlaneVertices r ∧
    ∃ y, P.graph.Adj x y ∧ E.vertexCoord y 0 < r}


def PeriodicPlaneEmbedding.lowerBoundaryRayVertices
    (E : PeriodicPlaneEmbedding P) (r s : ℝ) : Set V :=
  E.rightHalfPlaneBoundaryVertices r ∩ {x | E.vertexCoord x 1 ≤ s}


def PeriodicPlaneEmbedding.upperBoundaryRayVertices
    (E : PeriodicPlaneEmbedding P) (r s : ℝ) : Set V :=
  E.rightHalfPlaneBoundaryVertices r ∩ {x | s ≤ E.vertexCoord x 1}

end StatMech.FK.PeriodicPlanar
