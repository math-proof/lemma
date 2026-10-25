/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6deficitform.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rmr_reflectinvolution.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc3_core.Part3
import Def.StatisticalMechanics.Code.Walls.rc6deficitform.Part2
open Finset
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc6_deficit_eq (A B : Set (ConfigSpace α)) :
    rc6_deficit A B =
      (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) : ℤ)
        - (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) : ℤ) :=
  rfl

open Classical in


theorem rc6_reimerCardForm_iff_deficit (A B : Set (ConfigSpace α)) :
    StatMech.poc_ReimerCardForm A B ↔ rc6_deficit A B ≤ 0 := by
  rw [rmr_reimerCardForm_iff_inter]
  unfold rc6_deficit
  omega


end StatMech.Walls
