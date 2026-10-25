/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyMonoRefute.Part2
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace


def refuteA : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = false ∧ ω 1 = false}


def refuteB : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}


def refuteTail : ConfigSpace (Fin 1) := fun _ => false


end StatMech
