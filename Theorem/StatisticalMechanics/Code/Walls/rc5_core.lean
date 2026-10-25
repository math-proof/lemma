/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc5_reflectinvolution.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc5_reindextransfer
import Theorem.StatisticalMechanics.Code.Walls.rc5_doubledboxcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc5_dpairsmodular
import Theorem.StatisticalMechanics.Code.Walls.rc5_itercompcard
import Theorem.StatisticalMechanics.Code.Walls.rc5_nonvacuity
import Theorem.StatisticalMechanics.Code.Walls.rc2_core.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


section Deficit

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc5_core_reimerCardForm_iff_deficit (A B : Set (ConfigSpace α)) :
    StatMech.poc_ReimerCardForm A B ↔ rc5_deficit A B ≤ 0 :=
  rc5_reimerCardForm_iff_deficit A B


theorem rc5_core_deficitNonpos_iff_reimerCardFormAll :
    rc5_DeficitNonpos ↔ ReimerCardFormAll :=
  rc5_deficitNonpos_iff_reimerCardFormAll

end Deficit


section Engine

variable {β : Type*} [DecidableEq β]


theorem rc5_core_compressionEngine (𝒜 ℬ : Finset (Finset β)) :
    ((boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ)
      ∧ (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ))
      ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ)
            - dpairsCount 𝒜 ℬ
          = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
            - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
                (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i))
      ∧ (∀ cs : List β, (iterDownComp cs 𝒜).card = 𝒜.card)
      ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β))
            ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ))
      ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β,
            dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
              ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
  refine ⟨rc5_doubled_box_count 𝒜 ℬ, fun i => rc5_dpairsCount_downDown_mono 𝒜 ℬ i,
    fun i => rc5_deficit_identity 𝒜 ℬ i, fun cs => rc5_iterDownComp_card cs 𝒜, ?_, ?_⟩
  · obtain ⟨cs, hcs, hmono, _⟩ := rc2_blendpoint_converges 𝒜
    exact ⟨cs, hcs, hmono ℬ⟩
  · intro h𝒜 hℬ i; exact rc2_blendpoint_favourable h𝒜 hℬ i

end Engine


section Reflection

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in


theorem rc5_core_reflectionDeficit (A B : Set (ConfigSpace α)) :
    Function.Involutive (rmr_compl : ConfigSpace α → ConfigSpace α)
      ∧ (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B))
          = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)))
      ∧ (StatMech.poc_ReimerCardForm A B ↔ rc5_deficit A B ≤ 0) :=
  ⟨rc5_compl_involutive, rc5_RHS_eq_inter A B, rc5_reimerCardForm_iff_deficit A B⟩

end Reflection


theorem rc5_core_reindexTransfer (hcard : ReimerCardFormAll)
    {β : Type*} [Fintype β] [DecidableEq β] (A B : Set (ConfigSpace β)) :
    poc_ReimerCardForm A B :=
  rc5_reindexTransfer hcard A B


end StatMech.Walls
