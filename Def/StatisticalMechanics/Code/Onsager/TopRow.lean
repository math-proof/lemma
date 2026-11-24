module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.WalkCrossing.Part4
public import Def.StatisticalMechanics.Code.Onsager.UmlaufsatzStrip
public import Theorem.StatisticalMechanics.Code.Onsager.TopRow


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TopRow.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager.TopRow

open Finset

open Fin.NatCast

open StatMech.Onsager.BaseCase

open StatMech.Onsager.NoDoubleWind

open StatMech.Onsager.WalkCrossing

variable {n : ℕ} [NeZero n]


def SingleTopRun (d : Fin n → Fin 4) (M : Fin n) : Prop :=
  ∀ v : Fin n, (pos d v).2 = (pos d M).2 →
    ∃ j : ℕ, (∀ i : ℕ, i < j → d (M + (Nat.cast i : Fin n)) = 2) ∧
      (pos d v).1 = (pos d M).1 - (j : ℤ)


end StatMech.Onsager.TopRow
