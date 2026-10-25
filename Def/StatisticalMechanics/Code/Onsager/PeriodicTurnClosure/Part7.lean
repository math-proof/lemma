/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part6


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

def ons_periodicArcDirections {n : ℕ}
    (d : Fin n → Fin 4) (N : ℕ) (imin imax : Fin n) :
    List (Fin 4) :=
  (ons_periodicArcStates N imin imax).dropLast.map
    (fun z ↦ d z.2)

end StatMech.Onsager
