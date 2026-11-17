/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.BaseCase
public import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind

@[expose] public section

namespace StatMech.Onsager.WalkCrossing

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager.NoDoubleWind

variable {n : ℕ} [NeZero n]


def isVertEdge (w : Fin 4) : Prop := w = 1 ∨ w = 3


def isHorizEdge (w : Fin 4) : Prop := w = 0 ∨ w = 2

end StatMech.Onsager.WalkCrossing
