/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc3_slabcardiffperkey.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc3_slabimgeqinter.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc3_doubledboxcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc3_hallforswapinjection
import Theorem.StatisticalMechanics.Code.Walls.rc3_minimalwitnessencoded
import Theorem.StatisticalMechanics.Code.Walls.rc2_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_blendpoint
import Def.StatisticalMechanics.Code.Walls.rc3_core
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc3_core_reimerCardFormAll_of_slabCardAll (h : StatMech.poc_SlabCardAll) :
    ReimerCardFormAll :=
  fun n A B => poc_reimerCardForm_of_slabCard A B (h n A B)

open Classical in


theorem rc3_core_perKey_top_iff_reimerCardForm (A B : Set (ConfigSpace α)) :
    rc3_PerKey A B poc_topKey ↔
      #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤
        #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) :=
  rc3_perKey_top A B


theorem rc3_core_provedDAG {β : Type*} [DecidableEq β] (𝒜 ℬ : Finset (Finset β)) :
    ((boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ)
      ∧ (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ))
      ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ)
            - dpairsCount 𝒜 ℬ
          = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
            - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
                (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i))
      ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β))
            ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ))
      ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β,
            dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
              ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
  refine ⟨rc3_doubled_box_count 𝒜 ℬ, ?_, ?_, ?_, ?_⟩
  · intro i; exact rc2_dpairsCount_downDown_mono 𝒜 ℬ i
  · intro i; exact rc2_deficit_identity 𝒜 ℬ i
  · obtain ⟨cs, hcs, hmono, _⟩ := rc2_blendpoint_converges 𝒜
    exact ⟨cs, hcs, hmono ℬ⟩
  · intro h𝒜 hℬ i; exact rc2_blendpoint_favourable h𝒜 hℬ i


end StatMech.Walls
