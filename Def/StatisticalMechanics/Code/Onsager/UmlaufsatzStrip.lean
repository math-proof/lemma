/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzStrip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind2.Part2
import Theorem.StatisticalMechanics.Code.Onsager.UmlaufsatzStrip


namespace StatMech.Onsager.UmlaufsatzStrip

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager.NoDoubleWind

open StatMech.Onsager.NoDoubleWind2

variable {n : ℕ} [NeZero n]


def TopRowContiguous (d : Fin n → Fin 4) : Prop :=
  ∃ M : Fin n, (∀ j : Fin n, (pos d j).2 ≤ (pos d M).2) ∧
    ∀ a b : Fin n, (pos d a).2 = (pos d M).2 → (pos d b).2 = (pos d M).2 →
      ∀ x : ℤ, (pos d a).1 ≤ x → x ≤ (pos d b).1 →
        ∃ c : Fin n, pos d c = (x, (pos d M).2)

end StatMech.Onsager.UmlaufsatzStrip
