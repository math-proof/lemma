module
public import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite.Part5
public import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
open scoped BigOperators
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


def natAsReal (F : ConfigSpace E -> ℕ) : ConfigSpace E -> ℝ :=
  fun omega => F omega


def natUpperLevel (F : ConfigSpace E -> ℕ) (k : ℕ) : Set (ConfigSpace E) :=
  {omega | k < F omega}

end StatMech.FrontierA
