/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Mathlib.Data.Finset.Prod
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part2
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


def reimerStepCexA : Finset (Finset (Fin 2)) := {∅, {1}}


def reimerStepCexB : Finset (Finset (Fin 2)) := {∅, {0, 1}}


end StatMech
