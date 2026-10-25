/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldGridAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceClosure
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectangleLimit
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

def PeriodicPlaneEmbedding.BottomPreferred
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (N : Nat) (a b c d : Real) (z : Site 2) : Prop :=
  mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectTopBoundaryVertices a b c d)) <=
    mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectBottomBoundaryVertices a b c d))

def PeriodicPlaneEmbedding.TopPreferred
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (N : Nat) (a b c d : Real) (z : Site 2) : Prop :=
  mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectBottomBoundaryVertices a b c d)) <=
    mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectTopBoundaryVertices a b c d))

def PeriodicPlaneEmbedding.LeftPreferred
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (N : Nat) (a b c d : Real) (z : Site 2) : Prop :=
  mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectRightBoundaryVertices a b c d)) <=
    mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectLeftBoundaryVertices a b c d))

def PeriodicPlaneEmbedding.RightPreferred
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (N : Nat) (a b c d : Real) (z : Site 2) : Prop :=
  mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectLeftBoundaryVertices a b c d)) <=
    mu.real (E.rectSideConnectionEvent a b c d
      ((P.orbitBox N).image (P.shift z) : Set V)
      (E.rectRightBoundaryVertices a b c d))


end StatMech.FK.PeriodicPlanar
