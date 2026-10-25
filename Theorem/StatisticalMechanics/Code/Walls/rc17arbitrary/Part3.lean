/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc16sliceunion
import Theorem.StatisticalMechanics.Code.Walls.rc9core.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc8core.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyInjClose.Part2
import Def.StatisticalMechanics.Code.Walls.rc17arbitrary.Part2
open Finset MeasureTheory
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc17_spread_increasing_of_increasing {n : ℕ} {A : Set (ConfigSpace (Fin n))}
    (hA : IsIncreasing A) : IsIncreasing (rc17_spreadEvent A) := by
  intro η η' hηη' hη
  change (fun i => η' (Sum.inl i)) ∈ A
  refine hA (fun i => ?_) hη
  exact hηη' (Sum.inl i)

open Classical in


theorem rc17_spread_not_increasing :
    ¬ IsIncreasing (rc17_spreadEvent rbi_A) := by
  intro hcon
  set botC : ConfigSpace (Fin 2 ⊕ Fin 2) := fun _ => false with hbot
  set topC : ConfigSpace (Fin 2 ⊕ Fin 2) := fun _ => true with htop
  have hle : botC ≤ topC := by intro x; simp [hbot, htop]
  have hbotmem : botC ∈ rc17_spreadEvent rbi_A := by
    change (fun i => botC (Sum.inl i)) ∈ rbi_A
    simp [rbi_A, hbot]
  have htopmem : topC ∈ rc17_spreadEvent rbi_A := hcon hle hbotmem
  have : (fun i => topC (Sum.inl i)) ∈ rbi_A := htopmem
  simp [rbi_A, htop] at this


end StatMech.Walls
