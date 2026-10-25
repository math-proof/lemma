/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_topkey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
import Theorem.StatisticalMechanics.Code.Walls.rmr_topkey
open Finset
open scoped FinsetFamily


namespace StatMech.Walls

open StatMech StatMech.ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


def ReimerCardForm (A B : Set (ConfigSpace α)) : Prop :=
  #(Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B)) ≤
    #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B))


end StatMech.Walls
