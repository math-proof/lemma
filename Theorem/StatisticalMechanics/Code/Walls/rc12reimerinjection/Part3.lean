/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc11core.Part3
import Def.StatisticalMechanics.Code.Walls.rc12reimerinjection.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in

theorem rc12_boxSuppComp_eq (𝒜 ℬ : Finset (Finset α)) :
    rc12_boxSuppComp 𝒜 ℬ = rc10_boxSupp 𝒜 ℬ := by
  ext S
  rw [rc12_boxSuppComp, rc11_mem_boxSupp]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨K, hK, L, hL, hd, hKS, hLS⟩; exact ⟨K, L, hd, hKS, hLS, hK, hL⟩
  · rintro ⟨K, L, hd, hKS, hLS, hK, hL⟩; exact ⟨K, hK, L, hL, hd, hKS, hLS⟩

open Classical in

theorem rc12_reflInterComp_eq (𝒜 ℬ : Finset (Finset α)) :
    rc12_reflInterComp 𝒜 ℬ = rc10_reflInter 𝒜 ℬ := by
  ext S
  rw [rc12_reflInterComp, rc11_mem_reflInter]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]


end StatMech.Walls
