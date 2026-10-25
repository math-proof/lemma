/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripMasses
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripFamilyMass


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexCS_mem_classIncidences_iff
    {T L : ℕ} {hT : 0 < T} {cls : HexPairedBoundaryClass}
    {e : HexCSIncidence T L} :
    e ∈ hexCSClassIncidences T L hT cls ↔
      e ∈ hexCSBoundaryIncidences T L ∧
        e ≠ hexCSStartIncidence T L hT ∧
        hexCSBoundaryClass e = cls := by
  rw [hexCSClassIncidences, Finset.mem_filter, Finset.mem_sdiff,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hbdry, hstart⟩, hcls⟩
    exact ⟨hbdry, hstart, hcls⟩
  · rintro ⟨hbdry, hstart, hcls⟩
    exact ⟨⟨hbdry, hstart⟩, hcls⟩


theorem hexCS_boundary_mid_injective {T L : ℕ}
    {e f : HexCSIncidence T L}
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hf : f ∈ hexCSBoundaryIncidences T L)
    (hm : hexAWMid e.vtx.1 e.edge = hexAWMid f.vtx.1 f.edge) :
    e = f := by
  rcases (hexAWMid_eq_iff e.vtx.1 f.vtx.1 e.edge f.edge).mp hm with
    ⟨hcoord, hedge⟩ | ⟨hcoord, hedge⟩
  · cases e with
    | mk ev ee =>
        cases f with
        | mk fv fe =>
            rw [HexIncidence.mk.injEq]
            exact ⟨Subtype.ext hcoord.symm, hedge.symm⟩
  · rw [hexCS_mem_boundary_iff] at he
    exfalso
    apply he
    unfold hexCSIsInterior
    rw [← hcoord]
    exact f.vtx.2

theorem hexCS_class_mid_injective
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass) :
    Set.InjOn (fun e : HexCSIncidence T L =>
      hexAWMid e.vtx.1 e.edge) (hexCSClassIncidences T L hT cls : Set _) := by
  intro e he f hf hm
  exact hexCS_boundary_mid_injective
    (hexCS_mem_classIncidences_iff.mp he).1
    (hexCS_mem_classIncidences_iff.mp hf).1 hm


end
end StatMech.Universality
