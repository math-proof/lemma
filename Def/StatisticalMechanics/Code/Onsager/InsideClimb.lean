/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InsideClimb.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.SingleTopRun
import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind2.Part2
import Theorem.StatisticalMechanics.Code.Onsager.InsideClimb


namespace StatMech.Onsager.InsideClimb

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.WalkCrossing
  StatMech.Onsager.NoDoubleWind StatMech.Onsager.JordanParity

variable {n : ℕ} [NeZero n]


def two_nw_corners_not_injective (d : Fin n → Fin 4) : Prop :=
  ∀ i j : Fin n, i ≠ j → d i = 1 → d (i + 1) = 2 → d j = 1 → d (j + 1) = 2 →
    ¬ Function.Injective (pos d)


end StatMech.Onsager.InsideClimb
