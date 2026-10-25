/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSubsystem.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeRectangularThermodynamic
import Theorem.StatisticalMechanics.Code.FrontierA.RectangularBlockTiling
import Instance.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.flexible false


namespace StatMech.FrontierA

noncomputable section

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

theorem gaugeSurfaceBoundary_union_of_disjoint
    (incidence : P → Finset E) {A B : Finset P} (hAB : Disjoint A B) :
    gaugeSurfaceBoundary incidence (A ∪ B) =
      gaugeSurfaceBoundary incidence A ∆ gaugeSurfaceBoundary incidence B := by
  ext e
  rw [mem_gaugeSurfaceBoundary]
  rw [mem_symmDiff, mem_gaugeSurfaceBoundary, mem_gaugeSurfaceBoundary]
  have hcount : plaquetteIncidenceCount incidence (A ∪ B) e =
      plaquetteIncidenceCount incidence A e + plaquetteIncidenceCount incidence B e := by
    unfold plaquetteIncidenceCount
    rw [Finset.sum_union hAB]
  rw [hcount, Nat.even_add]
  tauto

variable {Esmall Ebig Psmall Pbig : Type*}
  [Fintype Esmall] [DecidableEq Esmall] [Fintype Ebig] [DecidableEq Ebig]
  [Fintype Psmall] [DecidableEq Psmall] [Fintype Pbig] [DecidableEq Pbig]

theorem plaquetteIncidenceCount_map_apply
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (A : Finset Psmall) (e : Esmall) :
    plaquetteIncidenceCount incidenceBig (A.map pEmb) (eEmb e) =
      plaquetteIncidenceCount incidenceSmall A e := by
  unfold plaquetteIncidenceCount
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hinc]
  simp

theorem plaquetteIncidenceCount_map_apply_of_not_mem_range
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (A : Finset Psmall) {e : Ebig} (he : e ∉ Set.range eEmb) :
    plaquetteIncidenceCount incidenceBig (A.map pEmb) e = 0 := by
  unfold plaquetteIncidenceCount
  apply Finset.sum_eq_zero
  intro q hq
  rw [Finset.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  rw [hinc]
  have hnot : ¬∃ x ∈ incidenceSmall p, eEmb x = e :=
    fun ⟨x, _, hxe⟩ => he ⟨x, hxe⟩
  simp [Finset.mem_map, hnot]

theorem gaugeSurfaceBoundary_map
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (A : Finset Psmall) :
    gaugeSurfaceBoundary incidenceBig (A.map pEmb) =
      (gaugeSurfaceBoundary incidenceSmall A).map eEmb := by
  ext e
  by_cases he : e ∈ Set.range eEmb
  · obtain ⟨e', rfl⟩ := he
    rw [mem_gaugeSurfaceBoundary, plaquetteIncidenceCount_map_apply
      incidenceSmall incidenceBig eEmb pEmb hinc]
    simp [mem_gaugeSurfaceBoundary]
  · rw [mem_gaugeSurfaceBoundary,
      plaquetteIncidenceCount_map_apply_of_not_mem_range incidenceSmall
        incidenceBig eEmb pEmb hinc A he]
    have hnotmap : e ∉ (gaugeSurfaceBoundary incidenceSmall A).map eEmb := by
      intro hmem
      rw [Finset.mem_map] at hmem
      obtain ⟨e', _, heq⟩ := hmem
      exact he ⟨e', heq⟩
    simp [hnotmap]


end
end StatMech.FrontierA
