/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWLoopWeight
import Theorem.StatisticalMechanics.Code.Onsager.ShermanAssembly1
import Theorem.StatisticalMechanics.Code.Onsager.ShermanAssembly2


namespace StatMech.Onsager

open Matrix BigOperators Finset


def ons_loopRev (L : ℕ) {n : ℕ} [NeZero n] (v : Fin n → ons_Dart L) : Fin n → ons_Dart L :=
  fun k => ons_dartRev L (v (-k))


end StatMech.Onsager
