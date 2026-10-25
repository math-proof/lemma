/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

def PeriodicPlaneEmbedding.rectBottomBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) : Set V :=
  {x | x ∈ E.rectVertices a b c d ∧
    ∃ y, P.graph.Adj x y ∧ E.vertexCoord y 1 < c}

def PeriodicPlaneEmbedding.rectTopBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) : Set V :=
  {x | x ∈ E.rectVertices a b c d ∧
    ∃ y, P.graph.Adj x y ∧ d < E.vertexCoord y 1}

def PeriodicPlaneEmbedding.rectLeftBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) : Set V :=
  {x | x ∈ E.rectVertices a b c d ∧
    ∃ y, P.graph.Adj x y ∧ E.vertexCoord y 0 < a}

def PeriodicPlaneEmbedding.rectRightBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) : Set V :=
  {x | x ∈ E.rectVertices a b c d ∧
    ∃ y, P.graph.Adj x y ∧ b < E.vertexCoord y 0}


def PeriodicPlaneEmbedding.rectSideConnectionEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (S side : Set V) : Set (ConfigSpace (Sym2 V)) :=
  P.infiniteSetConnectionWithin (E.rectVertices a b c d) S side

end StatMech.FK.PeriodicPlanar
