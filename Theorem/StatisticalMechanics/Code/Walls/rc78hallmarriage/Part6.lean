/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc77configmeasure.Part4
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part5
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


set_option maxRecDepth 8000 in


theorem rc78_not_left_regular_fin2 :
    ∃ p ∈ rc75_sourceF rc75_wA rc75_wB, ∃ q ∈ rc75_sourceF rc75_wA rc75_wB,
      rc78_leftDeg rc75_wA rc75_wB p ≠ rc78_leftDeg rc75_wA rc75_wB q := by decide


open Classical in


theorem rc78_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc77_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in 


theorem rc78_status :
    
    (∀ (m : ℕ) (i : Fin m) (p : ConfigSpace (Fin m) × ConfigSpace (Fin m)),
        rc78_colType (swapAt i p) = rc78_colType p) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)), rc78_PerOrbitDom A B →
        ∃ f : (rc75_sourceF A B) → (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)),
          Function.Injective f ∧ ∀ p : (rc75_sourceF A B), f p ∈ rc78_nbhd A B (p : _)) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        (∃ f : (rc75_sourceF A B) → (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)),
          Function.Injective f ∧ ∀ p : (rc75_sourceF A B), f p ∈ rc78_nbhd A B (p : _)) →
        2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card) ∧
    
    (rc78_PerOrbitDom rc75_wA rc75_wB) ∧
    (∃ p ∈ rc75_sourceF rc75_wA rc75_wB, ∃ q ∈ rc75_sourceF rc75_wA rc75_wB,
        rc78_leftDeg rc75_wA rc75_wB p ≠ rc78_leftDeg rc75_wA rc75_wB q) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun _m i p => rc78_swapAt_colType i p,
   rc78_existsInjective_of_perOrbitDom,
   rc78_count_of_existsInjective,
   rc78_perOrbitDom_rc72_witness,
   rc78_not_left_regular_fin2,
   rc78_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
