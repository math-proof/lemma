/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc59doubledcover.Part5
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Def.StatisticalMechanics.Code.Walls.rc60reimerinjection
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


open Classical in


theorem rc60_famCylBoxResidue_of_boxUnionBound (h : rc60_BoxUnionBound) : rc20_FamCylBoxResidue :=
  fun m 𝒜 ℬ => rc60_wall_of_boxUnionBound 𝒜 ℬ (h m 𝒜 ℬ)

open Classical in


theorem rc60_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc18_reimerWprobCore_of_cylBoxReflInter
    (rc20_cylBoxReflInter_of_famCylBoxResidue (rc60_famCylBoxResidue_of_boxUnionBound h))

open Classical in


theorem rc60_boxUnionBound_of_indepHall_global (h : rc59_IndepHall) : rc60_BoxUnionBound :=
  fun m 𝒜 ℬ => rc60_boxUnionBound_of_indepHall h m 𝒜 ℬ


open Classical in


theorem rc60_boxUnionBound_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ)) :=
  rc59_indepHall_fin2 𝒜 ℬ (rc20_famCylBox 𝒜 ℬ)
    (Finset.mem_powerset.mpr (Finset.Subset.refl _))

open Classical in


theorem rc60_boxUnionBound_fin3_refuter :
    #(rc20_famCylBox rc32_A3 rc32_B3)
      ≤ #((rc20_famCylBox rc32_A3 rc32_B3).biUnion (rc59_nbhd rc32_A3 rc32_B3)) :=
  rc59_indepHall_fin3_refuter (rc20_famCylBox rc32_A3 rc32_B3)
    (Finset.mem_powerset.mpr (Finset.Subset.refl _))

open Classical in

theorem rc60_wall_fin3_refuter :
    #(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3) :=
  rc60_wall_of_boxUnionBound rc32_A3 rc32_B3 rc60_boxUnionBound_fin3_refuter

set_option maxRecDepth 4000 in


theorem rc60_reflInter_not_compression_invariant :
    (rc20_reflInterComp 2 (Down.compression 0 ({{0}} : Finset (Finset (Fin 2)))) ({{1}})).card
      ≠ (rc20_reflInterComp 2 ({{0}}) ({{1}})).card := by
  decide


end StatMech.Walls
