module
public import Theorem.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part5
public import Mathlib.Combinatorics.Hall.Basic
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part2
open Finset MeasureTheory
open scoped NNReal FinsetFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def PerOrbitCardAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), PerOrbitCard A B


end StatMech
