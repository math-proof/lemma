/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc63doubledinjection.Part3
import Def.StatisticalMechanics.Code.Walls.rc64consolidation.Part3
set_option linter.style.longLine false


set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


set_option maxHeartbeats 4000000 in 
set_option maxRecDepth 10000 in
open Classical in


theorem rc64_marriage_fin3_ex2 :
    ∀ 𝒯 ∈ (rc20_famCylBox rc64_A3ex2 rc64_B3ex2).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc64_A3ex2 rc64_B3ex2)).card :=
  (rc59_indepHall_pair_iff rc64_A3ex2 rc64_B3ex2).mpr
    (rc33_hallOneSidedA_prop_of_bool 3 rc64_A3ex2 rc64_B3ex2 (by rw [rc64_A3ex2, rc64_B3ex2]; decide))


theorem rc64_status :
    
    (rc64_ReimerLeaf → ReimerWprobCore) ∧
    
    (rc64_BoxUnionBound → ReimerWprobCore) ∧
    
    (rc64_ReimerLeaf → rc64_BoxUnionBound) ∧
    
    (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) (𝒯 : Finset (Finset (Fin m))),
        𝒯 ⊆ rc20_famCylBox 𝒜 ℬ → 𝒯.card ≤ 1 →
        𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧
    
    (∀ (𝒜 ℬ : Finset (Finset (Fin 2))), ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
        𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧
    
    (∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset,
        𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc32_A3 rc32_B3)).card) ∧
    
    (∀ (Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ),
        (∀ (i : Fin 2) (p : _), Φ (rc62_step i p) = Φ p) →
        (∀ p, (rc20_famCylBoxComp 2 p.1 p.2).card ≤ Φ p) →
        (∀ p, Φ p ≤ (rc20_reflInterComp 2 p.1 p.2).card) → False) :=
  ⟨rc64_reimerWprobCore_of_leaf,
   rc64_reimerWprobCore_of_boxUnionBound,
   rc64_boxUnionBound_of_leaf,
   fun _ 𝒜 ℬ 𝒯 h𝒯 hcard => rc64_marriage_card_le_one 𝒜 ℬ 𝒯 h𝒯 hcard,
   rc64_marriage_fin2,
   rc64_marriage_fin3_refuter,
   rc62_no_invariant_sandwich⟩

end StatMech.Walls
