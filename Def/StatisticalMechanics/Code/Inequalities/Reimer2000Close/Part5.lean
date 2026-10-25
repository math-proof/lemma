/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerPairWitnessClose.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part4
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def r2k_rbi_swap : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) → (Fin 2 → Bool) :=
  fun p => fun a =>
    if a = 0 then (p.2 0 && !p.2 1)
    else (p.2 0 && !p.2 1 && p.1 1)


end StatMech
