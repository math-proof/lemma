module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
public import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
public import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part8
open Filter MeasureTheory Set SimpleGraph Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


def PeriodicPlaneEmbedding.finiteHorizontalCrossing
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    Set (ConfigSpace (Sym2 (E.RectVertex a b c d))) :=
  {eta | ∃ x y : E.RectVertex a b c d,
    E.rectLeftBoundary a b c d x ∧ E.rectRightBoundary a b c d y ∧
      (FK.openSub (E.rectGraph a b c d) eta).Reachable x y}


def PeriodicPlaneEmbedding.horizontalCrossingEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    Set (ConfigSpace (Sym2 V)) :=
  E.rectRestrict a b c d ⁻¹' E.finiteHorizontalCrossing a b c d

end StatMech.FK.PeriodicPlanar
