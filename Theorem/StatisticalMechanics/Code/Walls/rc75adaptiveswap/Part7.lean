/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc74doubledwall
import Instance.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


set_option maxRecDepth 8000 in


theorem rc75_adaptivePlan_fin1 :
    ∀ A B : Finset (ConfigSpace (Fin 1)),
      2 ^ 1 * (rc75_disjOccF1 A B).card ≤ A.card * B.card →
      rc75_existsPlan1 (rc75_sourceF1 A B) (rc75_prodF1 A B) := by
  decide


open Classical in


theorem rc75_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc74_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in 


theorem rc75_status :
    
    (∀ (i : Fin 2) (c img : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))),
        (rc75_applyChoice i c img).card = img.card) ∧
    
    (∀ (m : ℕ) (i : Fin m) (pred : ConfigSpace (Fin m) × ConfigSpace (Fin m) → Prop)
        [DecidablePred pred], (∀ p, pred (swapAt i p) ↔ pred p) →
        Function.Bijective (coordSwap i pred)) ∧
    
    (∀ (m : ℕ) (A B : Set (ConfigSpace (Fin m))) (K : Finset (Fin m)) (i : Fin m),
        Disjoint K {i} → ∀ (ω₁ ω₂ : ConfigSpace (Fin m)),
        OccursOn A (K : Set (Fin m)) ω₁ → OccursOn B ({i} : Finset (Fin m)) ω₁ →
        (swapAt i (ω₁, ω₂)).1 ∈ A ∧ (swapAt i (ω₁, ω₂)).2 ∈ B) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card → rc75_existsAdaptivePlan A B) ∧
    
    rc75_existsAdaptivePlan rc75_wA rc75_wB ∧
    
    (rc75_existsPlanOrder [1, 0] (rc75_sourceF rc75_wA rc75_wB) (rc75_prodF rc75_wA rc75_wB)
      ∧ ¬ rc75_existsPlanOrder [0, 1] (rc75_sourceF rc75_wA rc75_wB) (rc75_prodF rc75_wA rc75_wB)) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun i c img => rc75_applyChoice_card i c img,
   fun _m i pred _inst horb => coordSwap_bijective i pred horb,
   fun _m A B _K _i hKi ω₁ ω₂ hA hB => swapAt_mapsInto_of_witness A B hKi ω₁ ω₂ hA hB,
   rc75_adaptivePlan_fin2,
   rc75_adaptive_succeeds_where_rc72_failed,
   ⟨rc75_order_dependence.1, rc75_order_dependence.2.1⟩,
   rc75_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
