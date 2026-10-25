/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc41hall.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc37doubledhall.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc42_traceSlice_disjoint_of_ne (𝒜 ℬ : Finset (Finset α)) (K S S' : Finset α)
    (h : S ∩ K ≠ S' ∩ K) :
    Disjoint (rc35_traceSlice 𝒜 ℬ K S) (rc35_traceSlice 𝒜 ℬ K S') := by
  rw [Finset.disjoint_left]
  intro R hR hR'
  rw [rc35_traceSlice, Finset.mem_filter] at hR hR'
  exact h (hR.2.symm.trans hR'.2)


end StatMech.Walls
