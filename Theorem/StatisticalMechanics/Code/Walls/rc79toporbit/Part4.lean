/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part6
import Def.StatisticalMechanics.Code.Walls.rc79toporbit.Part4
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in 


theorem rc79_split_induction_refuted_fin3 :
    (rc79_disjOcc3 rc79_rA rc79_rB).card = 2
    ∧ (rc79_disjOcc2 (rc79_slice2 false rc79_rA) (rc79_slice2 true rc79_rB)).card
        + (rc79_disjOcc2 (rc79_slice2 true rc79_rA) (rc79_slice2 false rc79_rB)).card = 1
    ∧ ¬ (rc79_disjOcc3 rc79_rA rc79_rB).card
          ≤ (rc79_disjOcc2 (rc79_slice2 false rc79_rA) (rc79_slice2 true rc79_rB)).card
            + (rc79_disjOcc2 (rc79_slice2 true rc79_rA) (rc79_slice2 false rc79_rB)).card := by
  refine ⟨?_, ?_, ?_⟩ <;> decide


open Classical in


theorem rc79_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc78_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in 


theorem rc79_status :
    
    (∀ (A B : Finset (ConfigSpace (Fin 2))) (w : ConfigSpace (Fin 2)),
        rc78_srcOrbit A B (rc79_diagTypeF w) ⊆ rc78_tgtOrbit A B (rc79_diagTypeF w)) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        ((rc78_srcOrbit A B rc79_topTypeF).card ≤ (rc78_tgtOrbit A B rc79_topTypeF).card)
          ↔ ((rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card)) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)), rc78_PerOrbitDom A B) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) ∧
    
    (¬ (rc79_disjOcc3 rc79_rA rc79_rB).card
          ≤ (rc79_disjOcc2 (rc79_slice2 false rc79_rA) (rc79_slice2 true rc79_rB)).card
            + (rc79_disjOcc2 (rc79_slice2 true rc79_rA) (rc79_slice2 false rc79_rB)).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨rc79_diag_orbit_dominates,
   rc79_top_orbit_is_wall,
   rc79_perOrbitDom_fin2,
   rc79_top_wall_fin2,
   rc79_split_induction_refuted_fin3.2.2,
   rc79_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
