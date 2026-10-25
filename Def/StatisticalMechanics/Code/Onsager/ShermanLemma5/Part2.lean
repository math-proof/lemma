/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma5.Part2


namespace StatMech.Onsager

open Matrix BigOperators


def ons_mir {n : ℕ} [NeZero n] (l m k : Fin n) : Fin n :=
  ⟨min (l.val + m.val - k.val) (n - 1), by have := NeZero.pos n; omega⟩


end StatMech.Onsager
