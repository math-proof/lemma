/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerPairWitnessClose.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part2
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def r2k_SwapInjection (A B : Set (ConfigSpace α)) : Prop :=
  ∃ σ : ConfigSpace α × ConfigSpace α → (α → Bool),
    (∀ p : ConfigSpace α × ConfigSpace α, p.1 ∈ disjointOccurrence A B →
        (swapPair σ p).1 ∈ A ∧ (swapPair σ p).2 ∈ B) ∧
    Set.InjOn (swapPair σ) {p : ConfigSpace α × ConfigSpace α | p.1 ∈ disjointOccurrence A B}


end StatMech
