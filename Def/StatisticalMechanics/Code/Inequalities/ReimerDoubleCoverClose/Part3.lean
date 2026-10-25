/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressionClose.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubleCoverClose.Part2
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rdc_DoubleCover (A B : Set (ConfigSpace α)) : Prop :=
  ∃ wit : ConfigSpace α → (α → Bool),
    (∀ ω ∈ disjointOccurrence A B, OccursOn A {a | wit ω a = true} ω) ∧
    (∀ ω ∈ disjointOccurrence A B, OccursOn B {a | wit ω a = false} ω) ∧
    Set.InjOn (bfly wit) {p : ConfigSpace α × ConfigSpace α | p.1 ∈ disjointOccurrence A B}


end StatMech
