/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusBaseSpin
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicPhase.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Onsager.BaseCase

def triangularPeriodStateCoord {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (z : Nat × Fin n) : Int × Int :=
  triangularIntPos d z.2 +
    z.1 • triangularPathDisplacement (List.ofFn d)

def triangularPeriodicArcDirections {n : Nat}
    (d : Fin n -> Fin 6) (N : Nat) (imin imax : Fin n) : List (Fin 6) :=
  (ons_periodicArcStates N imin imax).dropLast.map (fun z => d z.2)

end StatMech.FrontierA
