/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarParameterMonotonicity.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V]

def PeriodicGraph.bufferedRootBoundaryEvent (P : PeriodicGraph V) (n : Nat) :
    Set (ConfigSpace (Sym2 (P.BufferedVertex n))) :=
  {omega | ∃ v : P.BufferedVertex n, P.bufferedBoundary n v ∧
    (FK.openSub (P.bufferedGraph n) omega).Reachable (P.bufferedRoot n) v}

end StatMech.FK.PeriodicPlanar
