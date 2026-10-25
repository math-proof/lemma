/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc6deficitform.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc2_hallavailable
import Mathlib.Combinatorics.Hall.Basic
open Finset Function
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in

noncomputable def rc6_boxFinset (A B : Set (ConfigSpace α)) : Finset (ConfigSpace α) :=
  Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)

open Classical in


noncomputable def rc6_imgFinset (A B : Set (ConfigSpace α)) : Finset (ConfigSpace α) :=
  Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B)

end StatMech.Walls
