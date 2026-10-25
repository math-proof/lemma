/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


def PeriodicPlaneEmbedding.planeRect
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) : Set ℂ :=
  {p | a ≤ E.coordinates p 0 ∧ E.coordinates p 0 ≤ b ∧
    c ≤ E.coordinates p 1 ∧ E.coordinates p 1 ≤ d}

end StatMech.FK.PeriodicPlanar
