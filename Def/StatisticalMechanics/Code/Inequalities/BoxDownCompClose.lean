/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BoxDownCompClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part4
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace


def bdc2_A : Finset (Finset (Fin 2)) := {∅, {0}, {1}}


def bdc2_B : Finset (Finset (Fin 2)) := {∅, {0}, {0,1}}


noncomputable def bdc2_w : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2


def bdc2_FF : ConfigSpace (Fin 2) := ![false, false]


def bdc2_TF : ConfigSpace (Fin 2) := ![true, false]


def bdc2_TT : ConfigSpace (Fin 2) := ![true, true]

end StatMech
