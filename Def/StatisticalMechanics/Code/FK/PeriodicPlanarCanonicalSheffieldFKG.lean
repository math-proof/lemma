/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]


def PeriodicGraph.bufferedSetBoundaryEvent
    (P : PeriodicGraph V) (S : Set V) (n : Nat) :
    Set (ConfigSpace (Sym2 (P.BufferedVertex n))) :=
  {eta | exists x : P.BufferedVertex n, x.1 ∈ S ∧
    exists y : P.BufferedVertex n, P.bufferedBoundary n y ∧
      (FK.openSub (P.bufferedGraph n) eta).Reachable x y}

end StatMech.FK.PeriodicPlanar
