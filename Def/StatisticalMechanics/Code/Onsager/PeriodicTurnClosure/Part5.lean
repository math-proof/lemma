/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part4


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

def ons_periodStateCoord {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (z : ℕ × Fin n) : ℤ × ℤ :=
  pos d z.2 + z.1 • ons_pathDisplacement (List.ofFn d)

end StatMech.Onsager
