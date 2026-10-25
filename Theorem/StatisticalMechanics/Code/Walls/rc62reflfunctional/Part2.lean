/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc61doubledbutterfly.Part3
import Def.StatisticalMechanics.Code.Walls.rc62reflfunctional
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


set_option maxRecDepth 4000 in

theorem rc62_edge₁₂ : rc62_step 0 rc62_node₁ = rc62_node₂ := by
  rw [rc62_step, rc62_node₁, rc62_node₂]; refine Prod.ext ?_ ?_ <;> decide

set_option maxRecDepth 4000 in

theorem rc62_edge₃₂ : rc62_step 0 rc62_node₃ = rc62_node₂ := by
  rw [rc62_step, rc62_node₃, rc62_node₂]; refine Prod.ext ?_ ?_ <;> decide

set_option maxRecDepth 4000 in

theorem rc62_edge₃₄ : rc62_step 1 rc62_node₃ = rc62_node₄ := by
  rw [rc62_step, rc62_node₃, rc62_node₄]; refine Prod.ext ?_ ?_ <;> decide

set_option maxRecDepth 4000 in

theorem rc62_edge₅₄ : rc62_step 1 rc62_node₅ = rc62_node₄ := by
  rw [rc62_step, rc62_node₅, rc62_node₄]; refine Prod.ext ?_ ?_ <;> decide

set_option maxRecDepth 4000 in

theorem rc62_node₁_box : (rc20_famCylBoxComp 2 rc62_node₁.1 rc62_node₁.2).card = 1 := by
  rw [rc62_node₁]; decide

set_option maxRecDepth 4000 in

theorem rc62_node₅_refl : (rc20_reflInterComp 2 rc62_node₅.1 rc62_node₅.2).card = 0 := by
  rw [rc62_node₅]; decide

open Classical in


theorem rc62_no_invariant_sandwich
    (Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ)
    (hinv : ∀ (i : Fin 2) (p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2))),
      Φ (rc62_step i p) = Φ p)
    (hlo : ∀ p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)),
      (rc20_famCylBoxComp 2 p.1 p.2).card ≤ Φ p)
    (hhi : ∀ p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)),
      Φ p ≤ (rc20_reflInterComp 2 p.1 p.2).card) :
    False := by
  
  have h12 : Φ rc62_node₁ = Φ rc62_node₂ := by rw [← rc62_edge₁₂, hinv]
  have h32 : Φ rc62_node₃ = Φ rc62_node₂ := by rw [← rc62_edge₃₂, hinv]
  have h34 : Φ rc62_node₃ = Φ rc62_node₄ := by rw [← rc62_edge₃₄, hinv]
  have h54 : Φ rc62_node₅ = Φ rc62_node₄ := by rw [← rc62_edge₅₄, hinv]
  
  have h15 : Φ rc62_node₁ = Φ rc62_node₅ := by
    rw [h12, ← h32, h34, ← h54]
  
  have hlo1 : (1 : ℕ) ≤ Φ rc62_node₁ := by
    have := hlo rc62_node₁; rwa [rc62_node₁_box] at this
  have hhi5 : Φ rc62_node₅ ≤ 0 := by
    have := hhi rc62_node₅; rwa [rc62_node₅_refl] at this
  rw [h15] at hlo1
  omega


set_option maxRecDepth 4000 in


theorem rc62_uniform_overshoots_reflInter :
    (({∅, {0}} : Finset (Finset (Fin 2))).card * ({∅, {0}} : Finset (Finset (Fin 2))).card) / 4
        > (rc20_reflInterComp 2 ({∅, {0}}) ({∅, {0}})).card
    ∧ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) ({∅, {0}})).card
        ≤ (({∅, {0}} : Finset (Finset (Fin 2))).card * ({∅, {0}} : Finset (Finset (Fin 2))).card) / 4 := by
  refine ⟨?_, ?_⟩ <;> decide


end StatMech.Walls
