/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc11core.Part3
import Instance.StatisticalMechanics.Code.Walls.rc12reimerinjection
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in

theorem rc12_isUpperFin_iff (n : ℕ) (𝒜 : Finset (Finset (Fin n))) :
    rc12_isUpperFin n 𝒜 ↔ IsUpperSet (𝒜 : Set (Finset (Fin n))) := by
  constructor
  · intro h S T hST hS
    simp only [Finset.mem_coe] at hS ⊢
    exact h S hS T (Finset.le_iff_subset.mp hST)
  · intro h S hS T hST
    have := h (Finset.le_iff_subset.mpr hST) (by simpa using hS)
    simpa using this


end StatMech.Walls
