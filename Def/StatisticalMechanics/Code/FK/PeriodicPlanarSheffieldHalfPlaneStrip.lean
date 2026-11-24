module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation.Part2
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneStrip
open Filter MeasureTheory Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

def PeriodicPlaneEmbedding.rightHalfPlaneStripVertices
    (E : PeriodicPlaneEmbedding P) (r : Real) (n : Nat) : Set V :=
  E.rightHalfPlaneVertices r ∩ {x | E.vertexCoord x 0 ≤ r + n}

end StatMech.FK.PeriodicPlanar
