/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part5


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

def ons_lastFin (n : ℕ) [NeZero n] : Fin n :=
  ⟨n - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne n)) (by omega)⟩

end StatMech.Onsager
