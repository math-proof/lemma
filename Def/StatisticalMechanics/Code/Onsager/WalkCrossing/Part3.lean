/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.BaseCase
import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind
import Theorem.StatisticalMechanics.Code.Onsager.WalkCrossing.Part2


namespace StatMech.Onsager.WalkCrossing

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager.NoDoubleWind

variable {n : ℕ} [NeZero n]


def onEdge (d : Fin n → Fin 4) (k : Fin n) (p : ℤ × ℤ) : Prop :=
  (min (pos d k).1 (pos d (k + 1)).1 ≤ p.1 ∧ p.1 ≤ max (pos d k).1 (pos d (k + 1)).1) ∧
    (min (pos d k).2 (pos d (k + 1)).2 ≤ p.2 ∧ p.2 ≤ max (pos d k).2 (pos d (k + 1)).2)


end StatMech.Onsager.WalkCrossing
