/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc2_slabcardallisbridge
import Theorem.StatisticalMechanics.Code.Walls.rc2_slabimgeqinter.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc2_cardformiffinter
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_doubledboxcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc2_blendpoint
import Def.StatisticalMechanics.Code.Walls.rc2_core.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc2_slabCardAll_of_slabInjectionAll (h : SlabInjectionAll) : StatMech.poc_SlabCardAll :=
  fun n A B => rc2_slabInjection_imp_slabCard (h n A B)


theorem rc2_reimerWprobCore_of_slabInjectionAll (h : SlabInjectionAll) : ReimerWprobCore :=
  rc2_reimerWprobCore_of_slabCardAll (rc2_slabCardAll_of_slabInjectionAll h)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem rc2_reimer_inequality_of_slabInjectionAll (h : SlabInjectionAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : NNReal} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  rc2_reimer_inequality_of_bridge
    (rc2_countBoxBridge_iff_slabCardAll.mpr (rc2_slabCardAll_of_slabInjectionAll h)) hp A B


theorem rc2_compressionEngine {β : Type*} [DecidableEq β] (𝒜 ℬ : Finset (Finset β)) :
    (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ))
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
  refine ⟨fun i => rc2_dpairsCount_downDown_mono 𝒜 ℬ i,
    fun i => rc2_deficit_identity 𝒜 ℬ i, ?_,
    fun h𝒜 hℬ i => rc2_blendpoint_favourable h𝒜 hℬ i⟩
  obtain ⟨cs, hcs, hmono, _⟩ := rc2_blendpoint_converges 𝒜
  exact ⟨cs, hcs, hmono ℬ⟩


theorem rc2_engine_count_eq_doubledBox {β : Type*} [DecidableEq β] (𝒜 ℬ : Finset (Finset β)) :
    (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ :=
  rc2_doubled_box_count 𝒜 ℬ


theorem rc2_slabCard_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    poc_SlabCard A B :=
  poc_slabCard_of_disjoint_support hA hB hST


theorem rc2_slabCard_one (A B : Set (ConfigSpace (Fin 1))) : poc_SlabCard A B :=
  rc_core_bridge_one A B


theorem rc2_slabCard_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : poc_SlabCard A B :=
  poc_slabCard_of_box_empty hbox


theorem rc2_slabCard_rbi : poc_SlabCard rbi_A rbi_B :=
  poc_slabCard_rbi

open Classical in


theorem rc2_perKey_rbi (k : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    #(Finset.univ.filter (fun ω => ω ∈ disjointOccurrence rbi_A rbi_B ∧ ω ∈ rc2_slab k)) ≤
      #(Finset.univ.filter (fun ω => ω ∈ rbi_A ∩ rc2_keyReflect k rbi_B ∧ ω ∈ rc2_slab k)) :=
  (rc2_slabCard_iff_perKey rbi_A rbi_B).mp poc_slabCard_rbi k


theorem rc2_slabInjection_rbi : SlabInjection rbi_A rbi_B :=
  (rc2_slabInjection_iff rbi_A rbi_B).mpr poc_slabCard_rbi

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in

theorem rc2_slabInjection_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    SlabInjection A B :=
  (rc2_slabInjection_iff A B).mpr (poc_slabCard_of_disjoint_support hA hB hST)


theorem rc2_slabInjection_one (A B : Set (ConfigSpace (Fin 1))) : SlabInjection A B :=
  (rc2_slabInjection_iff A B).mpr (rc_core_bridge_one A B)


open Classical in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem rc2_count_box_bridge :
    (∀ {α : Type} [Fintype α] [DecidableEq α] (A B : Set (ConfigSpace α)),
        poc_SlabCard A B ↔
          ∀ k : ConfigSpace α × ConfigSpace α,
            #(Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k)) ≤
            #(Finset.univ.filter (fun ω => ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k)))
      ∧ (SlabInjectionAll → StatMech.poc_SlabCardAll)
      ∧ (SlabInjectionAll → rc_core_CountBoxBridge)
      ∧ (SlabInjectionAll → ReimerWprobCore) := by
  refine ⟨fun {α} _ _ A B => rc2_slabCard_iff_perKey A B,
    rc2_slabCardAll_of_slabInjectionAll,
    fun h => rc2_countBoxBridge_iff_slabCardAll.mpr (rc2_slabCardAll_of_slabInjectionAll h),
    rc2_reimerWprobCore_of_slabInjectionAll⟩

end StatMech.Walls
