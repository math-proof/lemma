/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc5_reflectinvolution.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc5_reindextransfer
import Theorem.StatisticalMechanics.Code.Walls.rc5_doubledboxcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc5_dpairsmodular
import Theorem.StatisticalMechanics.Code.Walls.rc5_itercompcard
import Theorem.StatisticalMechanics.Code.Walls.rc5_nonvacuity
import Theorem.StatisticalMechanics.Code.Walls.rc2_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc5_core
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


section Injection

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in


def rc5_BoxReflectInjection (A B : Set (ConfigSpace α)) : Prop :=
  ∃ f : ConfigSpace α → ConfigSpace α,
    Set.InjOn f {ω | ω ∈ disjointOccurrence A B} ∧
    ∀ ω, ω ∈ disjointOccurrence A B → f ω ∈ A ∩ rmr_reflect B

end Injection
end StatMech.Walls
