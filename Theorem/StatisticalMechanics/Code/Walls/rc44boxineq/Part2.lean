/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc43reimer.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc44boxineq.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in

theorem rc44_famCylBoxEComp_eq (E : Finset α) (𝒜 ℬ : Finset (Finset α)) :
    rc44_famCylBoxEComp E 𝒜 ℬ = rc44_famCylBoxE E 𝒜 ℬ := by
  ext S
  rw [rc44_famCylBoxEComp, Finset.mem_filter, Finset.mem_powerset, rc44_mem_famCylBoxE]
  refine and_congr_right (fun hSE => ?_)
  constructor
  · rintro ⟨p, hp⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    obtain ⟨⟨hKE, hLE⟩, hKL, hKA, hLB⟩ := hp
    exact ⟨p.1, p.2, hKE, hLE, hKL,
      fun T hT => hKA T (Finset.mem_powerset.mpr hT),
      fun T hT => hLB T (Finset.mem_powerset.mpr hT)⟩
  · rintro ⟨K, L, hKE, hLE, hKL, hKA, hLB⟩
    refine ⟨(K, L), ?_⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
    exact ⟨⟨hKE, hLE⟩, hKL, fun T hT => hKA T (Finset.mem_powerset.mp hT),
      fun T hT => hLB T (Finset.mem_powerset.mp hT)⟩

open Classical in

theorem rc44_reflInterEComp_eq (E : Finset α) (𝒜 ℬ : Finset (Finset α)) :
    rc44_reflInterEComp E 𝒜 ℬ = rc44_reflInterE E 𝒜 ℬ := by
  rfl


end StatMech.Walls
