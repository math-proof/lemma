/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyInjClose.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerPairWitnessClose
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rpw_PairDoubleCover (A B : Set (ConfigSpace α)) : Prop :=
  ∃ wit : ConfigSpace α × ConfigSpace α → (α → Bool),
    (∀ p : ConfigSpace α × ConfigSpace α, p.1 ∈ disjointOccurrence A B →
        OccursOn A {a | wit p a = true} p.1) ∧
    (∀ p : ConfigSpace α × ConfigSpace α, p.1 ∈ disjointOccurrence A B →
        OccursOn B {a | wit p a = false} p.1) ∧
    Set.InjOn (bfly2 wit) {p : ConfigSpace α × ConfigSpace α | p.1 ∈ disjointOccurrence A B}


def rpw_p1 : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) :=
  (rbi_cfg false false, rbi_cfg false true)


def rpw_p2 : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) :=
  (rbi_cfg false true, rbi_cfg false false)


end StatMech
