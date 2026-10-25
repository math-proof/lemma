/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc21persupport.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_blendpoint
import Theorem.StatisticalMechanics.Code.Walls.rc16sliceunion
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Def.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


variable {β : Type*} [DecidableEq β]


open Classical in


theorem rc22_famCylBox_iterDownComp_mono (h : rc22_BoxCompressionMono) {n : ℕ}
    (cs : List (Fin n)) (𝒜 ℬ : Finset (Finset (Fin n))) :
    #(rc20_famCylBox 𝒜 ℬ)
      ≤ #(rc20_famCylBox (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) := by
  induction cs with
  | nil => rw [iterDownComp_nil, iterDownComp_nil]
  | cons i cs ih =>
    rw [iterDownComp_cons, iterDownComp_cons]
    exact le_trans ih (h n _ _ i)

open Classical in


theorem rc22_famCylBoxResidue_of_boxCompression
    (hmono : rc22_BoxCompressionMono) (hbase : rc22_BoxDownsetBase) :
    rc20_FamCylBoxResidue := by
  intro n 𝒜 ℬ
  obtain ⟨cs, hcs𝒜, hcsℬ, _, _, _⟩ := rc2_blendpoint_pair 𝒜 ℬ
  calc #(rc20_famCylBox 𝒜 ℬ)
      ≤ #(rc20_famCylBox (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) :=
        rc22_famCylBox_iterDownComp_mono hmono cs 𝒜 ℬ
    _ ≤ #(rc10_reflInter (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) :=
        hbase n _ _ hcs𝒜 hcsℬ
    _ ≤ #(rc10_reflInter 𝒜 ℬ) := rc22_reflInter_iterDownComp_antitone cs 𝒜 ℬ


theorem rc22_cylBoxReflInter_of_boxCompression
    (hmono : rc22_BoxCompressionMono) (hbase : rc22_BoxDownsetBase) :
    rc18_CylBoxReflInter :=
  rc20_famCylBoxResidue_iff_cylBoxReflInter.mp
    (rc22_famCylBoxResidue_of_boxCompression hmono hbase)


open Classical in


theorem rc22_boxDownsetBase_fin0 (𝒜 ℬ : Finset (Finset (Fin 0))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc20_famCylBox_fin0 𝒜 ℬ

open Classical in


theorem rc22_boxDownsetBase_upperSet {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin n))}
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin n)))) (hℬ : IsUpperSet (ℬ : Set (Finset (Fin n)))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc22_famCylBox_le_reflInter_of_upperSet h𝒜 hℬ


set_option linter.unusedVariables false in
open Classical in


theorem rc22_reimer_doublecover :
    (∀ (𝒜 ℬ : Finset (Finset α)), #(rc10_reflInter 𝒜 ℬ) = #(rc22_complPairs 𝒜 ℬ))
      ∧ (∀ (𝒜 ℬ : Finset (Finset α)), rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rc22_complFam ℬ)
      ∧ (∀ (𝒜 ℬ : Finset (Finset α)), rc20_famCylBox 𝒜 ℬ ⊆ rc10_boxSupp 𝒜 ℬ)
      ∧ (rc22_InterCountResidue ↔ rc20_FamCylBoxResidue)
      ∧ (∀ [Fintype α] (i : α) (𝒜 ℬ : Finset (Finset α)),
          #(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ))
            ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc22_BoxCompressionMono → rc22_BoxDownsetBase → rc18_CylBoxReflInter) :=
  ⟨rc22_card_reflInter_eq_complPairs,
    rc22_reflInter_eq_inter_complFam,
    rc22_famCylBox_subset_boxSupp,
    rc22_interCountResidue_iff_famCylBoxResidue,
    fun i 𝒜 ℬ => rc22_reflInter_downDown_antitone i 𝒜 ℬ,
    rc22_cylBoxReflInter_of_boxCompression⟩

end StatMech.Walls
