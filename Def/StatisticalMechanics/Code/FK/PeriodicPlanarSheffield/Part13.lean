module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
public import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
public import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part12
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


def PeriodicGraph.translateEvent
    (P : PeriodicGraph V) (z : Site 2)
    (A : Set (ConfigSpace (Sym2 V))) :
    Set (ConfigSpace (Sym2 V)) :=
  P.configTranslate z ⁻¹' A

end StatMech.FK.PeriodicPlanar
