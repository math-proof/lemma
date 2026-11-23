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
public import Theorem.StatisticalMechanics.Code.Onsager.WalkCrossing

@[expose] public section

namespace StatMech.Onsager.WalkCrossing

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager.NoDoubleWind

variable {n : ℕ} [NeZero n]


def fullLineCross (d : Fin n → Fin 4) (m : ℤ) : ℕ :=
  (Finset.univ.filter (fun k : Fin n =>
    isVertEdge (d k) ∧ min ((pos d k).2) ((pos d (k + 1)).2) = m)).card


end StatMech.Onsager.WalkCrossing
