/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part2
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {E : Type*}


def evXor : Set (ConfigSpace (Fin 2)) := {ω | ω 0 ≠ ω 1}


def evXnor : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = ω 1}


end StatMech
