/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonArray.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonRectangle
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldSynchronization
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualTransverse.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalErgodicity.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [Countable V] [Countable W]
  [DecidableEq V] [DecidableEq W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


def PeriodicGraph.fourShiftTemplate (P : PeriodicGraph V) (S : Finset V)
    (zLeft zRight zBottom zTop : Site 2) : Finset V :=
  (S.image (P.shift zLeft) ∪ S.image (P.shift zRight)) ∪
    (S.image (P.shift zBottom) ∪ S.image (P.shift zTop))

end StatMech.FK.PeriodicPlanar
