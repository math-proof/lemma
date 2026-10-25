/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part9
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCrossingGluing.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictCriticalAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictNoCoexistenceClosure.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAspectComparison
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


def finiteEventIntersection {Omega : Type*} :
    List (Set Omega) -> Set Omega
  | [] => Set.univ
  | A :: events => A ∩ finiteEventIntersection events

end StatMech.FK.PeriodicPlanar
