module
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressionClose.Part2
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part4
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubleCoverClose.Part3
open Finset MeasureTheory
open scoped NNReal FinsetFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rdc_DoubleCoverAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), rdc_DoubleCover A B


end StatMech
