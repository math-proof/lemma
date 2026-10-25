/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc59doubledcover.Part5
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Def.StatisticalMechanics.Code.Walls.rc60reimerinjection.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


set_option maxHeartbeats 4000000 in 
set_option maxRecDepth 10000 in


theorem rc60_hallBothSided_fin3_refuted :
    rc33_hallBothSided 3 rc60_A3ex rc60_B3ex = false := by
  rw [rc60_A3ex, rc60_B3ex]; decide

set_option maxHeartbeats 4000000 in 
set_option maxRecDepth 10000 in


theorem rc60_hallOneSidedA_holds_fin3_contrast :
    rc33_hallOneSidedA 3 rc60_A3ex rc60_B3ex = true := by
  rw [rc60_A3ex, rc60_B3ex]; decide


open Classical in


theorem rc60_status :
    (rc60_BoxUnionBound → ReimerWprobCore) ∧
    (rc59_IndepHall → rc60_BoxUnionBound) ∧
    (∀ (𝒜 ℬ : Finset (Finset (Fin 2))),
        #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ))) ∧
    (#(rc20_famCylBox rc32_A3 rc32_B3)
        ≤ #((rc20_famCylBox rc32_A3 rc32_B3).biUnion (rc59_nbhd rc32_A3 rc32_B3))) ∧
    (#(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3)) ∧
    ((rc20_reflInterComp 2 (Down.compression 0 ({{0}} : Finset (Finset (Fin 2)))) ({{1}})).card
        ≠ (rc20_reflInterComp 2 ({{0}}) ({{1}})).card) ∧
    (rc33_hallBothSided 3 rc60_A3ex rc60_B3ex = false) ∧
    (rc33_hallOneSidedA 3 rc60_A3ex rc60_B3ex = true) :=
  ⟨rc60_reimerWprobCore_of_boxUnionBound, rc60_boxUnionBound_of_indepHall_global,
    rc60_boxUnionBound_fin2, rc60_boxUnionBound_fin3_refuter, rc60_wall_fin3_refuter,
    rc60_reflInter_not_compression_invariant, rc60_hallBothSided_fin3_refuted,
    rc60_hallOneSidedA_holds_fin3_contrast⟩

end StatMech.Walls
