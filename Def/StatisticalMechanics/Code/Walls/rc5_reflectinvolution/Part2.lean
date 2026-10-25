/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_reflectinvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rmr_reflectinvolution.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc3_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc5_reflectinvolution.Part2
open Finset
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


noncomputable def rc5_deficit (A B : Set (ConfigSpace α)) : ℤ :=
  (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) : ℤ)
    - (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) : ℤ)

end StatMech.Walls
