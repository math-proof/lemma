/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDualPair.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part5
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


def PeriodicGraph.bufferedTwoPointEvent (P : PeriodicGraph V) (N : ℕ)
    (x y : P.BufferedVertex N) :
    Set (ConfigSpace (Sym2 (P.BufferedVertex N))) :=
  {omega | (FK.openSub (P.bufferedGraph N) omega).Reachable x y}

end StatMech.FK.PeriodicPlanar
