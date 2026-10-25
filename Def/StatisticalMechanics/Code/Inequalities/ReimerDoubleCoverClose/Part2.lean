/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressionClose.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubleCoverClose
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def bfly (wit : ConfigSpace α → (α → Bool)) (p : ConfigSpace α × ConfigSpace α) :
    ConfigSpace α × ConfigSpace α :=
  (bglue (wit p.1) p.1 p.2, bglue (wit p.1) p.2 p.1)

end StatMech
