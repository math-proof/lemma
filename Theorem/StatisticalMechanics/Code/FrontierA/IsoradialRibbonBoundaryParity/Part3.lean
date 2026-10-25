/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualSubgraphSum.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsoradialRibbonBoundaryParity.Part2


namespace StatMech.FrontierA

open Finset Equiv

variable {D E : Type*} [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]


namespace RibbonPermutationSystem

variable (R : RibbonPermutationSystem E D)

omit [Fintype E] in
theorem partialEdgeFlip_insert (F : Finset E) (e : E)
    (he : e ∈ F -> False) :
    R.partialEdgeFlip (insert e F) =
      R.edgeFlip e * R.partialEdgeFlip F := by
  unfold partialEdgeFlip
  exact Finset.noncommProd_insert_of_notMem F e R.edgeFlip
    (R.edgeFlip_pairwise (insert e F)) he

omit [Fintype E] in
theorem boundaryPerm_insert_sign (F : Finset E) (e : E)
    (he : e ∈ F -> False) :
    ((Equiv.Perm.sign (R.boundaryPerm (insert e F)) : Units Int) : Int) =
      -((Equiv.Perm.sign (R.boundaryPerm F) : Units Int) : Int) := by
  rw [boundaryPerm, partialEdgeFlip_insert R F e he, boundaryPerm]
  simp only [map_mul]
  rw [(R.edgeFlip_isSwap e).sign_eq]
  norm_num

omit [Fintype E] in


theorem boundaryComponents_insert_mod_two (F : Finset E) (e : E)
    (he : e ∈ F -> False) :
    R.boundaryComponents (insert e F) % 2 =
      (R.boundaryComponents F + 1) % 2 := by
  exact permCycleCount_mod_two_toggle_of_sign_neg _ _
    (R.boundaryPerm_insert_sign F e he)

omit [Fintype E] [DecidableEq E] in
@[simp] theorem boundaryPerm_empty :
    R.boundaryPerm (∅ : Finset E) = R.rotation := by
  unfold boundaryPerm partialEdgeFlip
  rw [Finset.noncommProd_empty, mul_one]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem boundaryComponents_empty :
    R.boundaryComponents (∅ : Finset E) =
      permCycleCount R.rotation := by
  simp [boundaryComponents]


theorem boundaryParity_eq_dualVertexCount
    (dualVertexCount : Nat)
    (hEuler : (Fintype.card E + permCycleCount R.rotation) % 2 =
      dualVertexCount % 2) :
    forall F : Finset E,
      (Fᶜ.card + R.boundaryComponents F) % 2 =
        dualVertexCount % 2 := by
  apply compl_card_add_boundary_mod_two_eq_dualVertexCount
    R.boundaryComponents dualVertexCount
  · exact R.boundaryComponents_insert_mod_two
  · simpa using hEuler

end RibbonPermutationSystem
end StatMech.FrontierA
