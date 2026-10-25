/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_cardformiffinter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rmr_topkey.Part2
import Theorem.StatisticalMechanics.Code.Walls.rmr_reflectinvolution.Part2
open Finset
open scoped StatMech FinsetFamily


namespace StatMech.Walls

open StatMech StatMech.ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


noncomputable def rc2_boxCard (A B : Set (ConfigSpace α)) : ℕ :=
  #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B))

open Classical in


noncomputable def rc2_interCard (A B : Set (ConfigSpace α)) : ℕ :=
  #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B))


noncomputable def rc2_deficit (A B : Set (ConfigSpace α)) : ℤ :=
  (rc2_boxCard A B : ℤ) - (rc2_interCard A B : ℤ)


end StatMech.Walls
