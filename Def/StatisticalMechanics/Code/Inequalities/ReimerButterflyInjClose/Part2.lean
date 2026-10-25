/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubleCoverClose.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyInjClose
open Finset
open scoped FinsetFamily


namespace StatMech

open ConfigSpace


def rbi_A : Set (ConfigSpace (Fin 2)) := {ω | ¬ (ω 0 = true ∧ ω 1 = true)}


def rbi_B : Set (ConfigSpace (Fin 2)) := {ω | ¬ (ω 0 = true ∧ ω 1 = false)}


end StatMech
