/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part3


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

def ons_periodStateList (n r : ℕ) : List (ℕ × Fin n) :=
  List.ofFn (fun i : Fin n ↦ (r, i))

def ons_allPeriodStates (n N : ℕ) : List (ℕ × Fin n) :=
  (List.range (N + 1)).flatMap (ons_periodStateList n)

def ons_periodicArcStates {n : ℕ} (N : ℕ)
    (imin imax : Fin n) : List (ℕ × Fin n) :=
  ((ons_allPeriodStates n N).drop imin.val).take
    (N * n + imax.val + 1 - imin.val)

end StatMech.Onsager
