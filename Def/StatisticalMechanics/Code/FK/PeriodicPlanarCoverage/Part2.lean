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
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


def PeriodicGraph.bufferedPairShell (P : PeriodicGraph V) (N : ℕ)
    (pairs : Finset (P.BufferedVertex N × P.BufferedVertex N)) :
    Set (ConfigSpace (Sym2 V)) :=
  ⋃ xy ∈ pairs, P.bufferedCylinder N
    (P.bufferedTwoPointEvent N xy.1 xy.2)

end StatMech.FK.PeriodicPlanar
