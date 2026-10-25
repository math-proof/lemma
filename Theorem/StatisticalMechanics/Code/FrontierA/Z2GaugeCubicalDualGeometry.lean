/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeMultibondAdapter.Part2
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

set_option maxHeartbeats 800000 in

theorem cubicalCellFaces_isClosed {a b c : Nat} (q : CubicalCell a b c) :
    IsClosedPlaquetteSet cubicalPlaquetteIncidence (cubicalCellFaces q) := by
  intro e
  rw [plaquetteIncidenceCount_eq_filter_card]
  rcases q with ⟨i, j, k⟩
  have hi : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hj : j.castSucc ≠ j.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hk : k.castSucc ≠ k.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  rw [Finset.card_filter]
  cases e with
  | x i' j' k' =>
      by_cases h0 : (i' = i ∧ j' = j.castSucc ∧ k' = k.castSucc)
      · rcases h0 with ⟨rfl, rfl, rfl⟩
        simp_all [cubicalCellFaces, cubicalPlaquetteIncidence]
      by_cases h1 : (i' = i ∧ j' = j.succ ∧ k' = k.castSucc)
      · rcases h1 with ⟨rfl, rfl, rfl⟩
        simp_all [cubicalCellFaces, cubicalPlaquetteIncidence]
      by_cases h2 : (i' = i ∧ j' = j.castSucc ∧ k' = k.succ)
      · rcases h2 with ⟨rfl, rfl, rfl⟩
        simp_all [cubicalCellFaces, cubicalPlaquetteIncidence]
      by_cases h3 : (i' = i ∧ j' = j.succ ∧ k' = k.succ)
      · rcases h3 with ⟨rfl, rfl, rfl⟩
        simp_all [cubicalCellFaces, cubicalPlaquetteIncidence]
      simp [cubicalCellFaces, cubicalPlaquetteIncidence, hi, hj, hk]
      all_goals split_ifs <;> norm_num <;> aesop
  | y i' j' k' =>
      by_cases h0 : (i' = i.castSucc ∧ j' = j ∧ k' = k.castSucc)
      · rcases h0 with ⟨rfl, rfl, rfl⟩
        simp_all [cubicalCellFaces, cubicalPlaquetteIncidence]
      by_cases h1 : (i' = i.succ ∧ j' = j ∧ k' = k.castSucc)
      · rcases h1 with ⟨rfl, rfl, rfl⟩
        simp_all [cubicalCellFaces, cubicalPlaquetteIncidence]
      by_cases h2 : (i' = i.castSucc ∧ j' = j ∧ k' = k.succ)
      · rcases h2 with ⟨rfl, rfl, rfl⟩
        simp_all [cubicalCellFaces, cubicalPlaquetteIncidence]
      by_cases h3 : (i' = i.succ ∧ j' = j ∧ k' = k.succ)
      · rcases h3 with ⟨rfl, rfl, rfl⟩
        simp_all [cubicalCellFaces, cubicalPlaquetteIncidence]
      simp [cubicalCellFaces, cubicalPlaquetteIncidence, hi, hj, hk]
      all_goals split_ifs <;> norm_num <;> aesop
  | z i' j' k' =>
      by_cases h0 : (i' = i.castSucc ∧ j' = j.castSucc ∧ k' = k)
      · rcases h0 with ⟨rfl, rfl, rfl⟩
        simp_all [cubicalCellFaces, cubicalPlaquetteIncidence]
      by_cases h1 : (i' = i.succ ∧ j' = j.castSucc ∧ k' = k)
      · rcases h1 with ⟨rfl, rfl, rfl⟩
        simp_all [cubicalCellFaces, cubicalPlaquetteIncidence]
      by_cases h2 : (i' = i.castSucc ∧ j' = j.succ ∧ k' = k)
      · rcases h2 with ⟨rfl, rfl, rfl⟩
        simp_all [cubicalCellFaces, cubicalPlaquetteIncidence]
      by_cases h3 : (i' = i.succ ∧ j' = j.succ ∧ k' = k)
      · rcases h3 with ⟨rfl, rfl, rfl⟩
        simp_all [cubicalCellFaces, cubicalPlaquetteIncidence]
      simp [cubicalCellFaces, cubicalPlaquetteIncidence, hi, hj, hk]
      all_goals split_ifs <;> norm_num <;> aesop


theorem closed_not_mem_of_unique_incident
    {E P : Type*} [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P]
    (incidence : P → Finset E) (A : Finset P)
    (hclosed : IsClosedPlaquetteSet incidence A)
    (p : P) (e : E) (hpe : e ∈ incidence p)
    (hunique : ∀ q ∈ A, e ∈ incidence q → q = p) :
    p ∉ A := by
  intro hp
  have hfilter : A.filter (fun q => e ∈ incidence q) = {p} := by
    ext q
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hqA, hqe⟩
      exact hunique q hqA hqe
    · intro hqp
      subst q
      exact ⟨hp, hpe⟩
  have heven := hclosed e
  rw [plaquetteIncidenceCount_eq_filter_card, hfilter] at heven
  norm_num at heven


theorem gaugeSurfaceBoundary_symmDiff
    {E P : Type*} [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P]
    (incidence : P → Finset E) (A B : Finset P) :
    gaugeSurfaceBoundary incidence (A ∆ B) =
      gaugeSurfaceBoundary incidence A ∆ gaugeSurfaceBoundary incidence B := by
  ext e
  simp only [mem_gaugeSurfaceBoundary, mem_symmDiff]
  rw [even_plaquetteIncidenceCount_symmDiff_iff]
  tauto


theorem gaugeSurfaceBoundary_insert
    {E P : Type*} [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P]
    (incidence : P → Finset E) (A : Finset P) (p : P) (hp : p ∉ A) :
    gaugeSurfaceBoundary incidence (insert p A) =
      incidence p ∆ gaugeSurfaceBoundary incidence A := by
  have hins : insert p A = ({p} : Finset P) ∆ A := by
    ext q
    simp only [mem_insert, mem_symmDiff, mem_singleton]
    by_cases hqp : q = p
    · subst q
      simp [hp]
    · simp [hqp]
  rw [hins, gaugeSurfaceBoundary_symmDiff,
    gaugeSurfaceBoundary_singleton]


end
end StatMech.FrontierA
