/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor.Part2


namespace StatMech.FrontierA

open Finset

open scoped BigOperators


variable {E : Type*} [Fintype E] [DecidableEq E]

namespace RibbonPermutationSystem

omit [Fintype E] [DecidableEq E] in
theorem edgeFlip_mul_self
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D) (edge : E) :
    R.edgeFlip edge * R.edgeFlip edge = 1 := by
  obtain ⟨a, b, hab, hswap⟩ := R.edgeFlip_isSwap edge
  rw [hswap]
  exact Equiv.swap_mul_self a b

omit [Fintype E] [DecidableEq E] in
theorem partialEdgeFlip_mul_self
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D) (F : Finset E) :
    R.partialEdgeFlip F * R.partialEdgeFlip F = 1 := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [partialEdgeFlip]
  | @insert edge F hedge ih =>
      rw [R.partialEdgeFlip_insert F edge (by simpa using hedge)]
      have hcomm : Commute (R.edgeFlip edge) (R.partialEdgeFlip F) := by
        unfold partialEdgeFlip
        apply Finset.noncommProd_commute
        intro other hother
        exact R.edgeFlip_commute edge other fun h =>
          hedge (h ▸ hother)
      rw [hcomm.symm.mul_mul_mul_comm, R.edgeFlip_mul_self edge, ih, mul_one]

theorem partialEdgeFlip_univ_mul
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D) (F : Finset E) :
    R.partialEdgeFlip Finset.univ * R.partialEdgeFlip F =
      R.partialEdgeFlip Fᶜ := by
  have hdisjoint : Disjoint Fᶜ F := disjoint_compl_left_iff.mpr le_rfl
  have hunion : Fᶜ ∪ F = (Finset.univ : Finset E) := by
    ext edge
    by_cases hedge : edge ∈ F <;> simp [hedge]
  have hsplit : R.partialEdgeFlip Finset.univ =
      R.partialEdgeFlip Fᶜ * R.partialEdgeFlip F := by
    unfold partialEdgeFlip
    rw [← hunion]
    exact Finset.noncommProd_union_of_disjoint hdisjoint R.edgeFlip
      (fun edge _ other _ hne => R.edgeFlip_commute edge other hne)
  rw [hsplit, mul_assoc, R.partialEdgeFlip_mul_self F, mul_one]


theorem dualRibbonSystem_boundaryPerm
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D) (F : Finset E) :
    R.dualRibbonSystem.boundaryPerm F = R.boundaryPerm Fᶜ := by
  change (R.rotation * R.partialEdgeFlip Finset.univ) *
      R.partialEdgeFlip F = R.rotation * R.partialEdgeFlip Fᶜ
  rw [mul_assoc, R.partialEdgeFlip_univ_mul F]

theorem dualRibbonSystem_boundaryComponents
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D) (F : Finset E) :
    R.dualRibbonSystem.boundaryComponents F =
      R.boundaryComponents Fᶜ := by
  unfold boundaryComponents
  rw [R.dualRibbonSystem_boundaryPerm F]


end RibbonPermutationSystem
end StatMech.FrontierA
