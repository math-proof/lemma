/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyInjClose.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerPairWitnessClose.Part2
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rpw_WeightInjection (A B : Set (ConfigSpace α)) : Prop :=
  ∃ Φ : ConfigSpace α × ConfigSpace α → ConfigSpace α × ConfigSpace α,
    (∀ p : ConfigSpace α × ConfigSpace α, p.1 ∈ disjointOccurrence A B →
        (Φ p).1 ∈ A ∧ (Φ p).2 ∈ B) ∧
    (∀ (φ : α → Bool → ℝ) (p : ConfigSpace α × ConfigSpace α), p.1 ∈ disjointOccurrence A B →
        pweight φ (Φ p).1 * pweight φ (Φ p).2 = pweight φ p.1 * pweight φ p.2) ∧
    Set.InjOn Φ {p : ConfigSpace α × ConfigSpace α | p.1 ∈ disjointOccurrence A B}


end StatMech
