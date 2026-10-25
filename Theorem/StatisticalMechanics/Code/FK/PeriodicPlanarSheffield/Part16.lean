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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part16
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem measurable_forceOpenFinset (F : Finset (Sym2 V)) :
    Measurable (forceOpenFinset F :
      ConfigSpace (Sym2 V) → ConfigSpace (Sym2 V)) :=
  measurable_pi_lambda _ fun e => by
    by_cases he : e ∈ F
    · simpa [forceOpenFinset, he] using (measurable_const :
        Measurable (fun _ : ConfigSpace (Sym2 V) => true))
    · simpa [forceOpenFinset, he] using ConfigSpace.measurable_eval e


end StatMech.FK.PeriodicPlanar
