/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part4
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


def poc_ReimerCardForm (A B : Set (ConfigSpace α)) : Prop :=
  #(Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B)) ≤
    #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B))


end StatMech
