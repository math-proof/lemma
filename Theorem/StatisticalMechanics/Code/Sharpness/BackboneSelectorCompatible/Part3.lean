/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2Quantitative
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Def.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part3
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]


theorem shb_mapLe_restrictBackbonePath
    {H G : SimpleGraph V} [DecidableRel G.Adj]
    (hHG : H ≤ G) (n : Current V) (hSupp : shb_CurrentSupportedOn H n)
    {x y : V} (p : G.Path x y) (hp : shb_IsBackboneOf G n x y p) :
    (⟨(shb_restrictBackbonePath hHG n hSupp p hp).1.mapLe hHG,
        (shb_restrictBackbonePath hHG n hSupp p hp).2.mapLe hHG⟩ :
      G.Path x y) = p := by
  apply Subtype.ext
  apply SimpleGraph.Walk.support_injective
  rw [SimpleGraph.Walk.support_mapLe_eq_support]
  exact SimpleGraph.Walk.support_transfer _ _


theorem shb_restrictBackbonePath_isBackbone
    {H G : SimpleGraph V} [DecidableRel G.Adj]
    (hHG : H ≤ G) (n : Current V) (hSupp : shb_CurrentSupportedOn H n)
    {x y : V} (p : G.Path x y) (hp : shb_IsBackboneOf G n x y p) :
    shb_IsBackboneOf H n x y (shb_restrictBackbonePath hHG n hSupp p hp) := by
  intro e he
  apply hp e
  simpa [shb_restrictBackbonePath, SimpleGraph.Walk.edges_transfer] using he


theorem shb_mapLe_isBackboneOf
    {H G : SimpleGraph V} (hHG : H ≤ G) (n : Current V) {x y : V}
    (p : H.Path x y) (hp : shb_IsBackboneOf H n x y p) :
    shb_IsBackboneOf G n x y
      ⟨p.1.mapLe hHG, p.2.mapLe hHG⟩ := by
  intro e he
  apply hp e
  simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he


theorem shb_backboneSet_nonempty_iff_of_supported
    {H G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (n : Current V) (hSupp : shb_CurrentSupportedOn H n)
    (x y : V) :
    (shb_backboneSet H n x y).Nonempty ↔
      (shb_backboneSet G n x y).Nonempty := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨shb_pathMapLe hHG p, ?_⟩
    rw [shb_mem_backboneSet] at hp ⊢
    exact shb_mapLe_isBackboneOf hHG n p hp
  · rintro ⟨p, hp⟩
    rw [shb_mem_backboneSet] at hp
    refine ⟨shb_restrictBackbonePath hHG n hSupp p hp, ?_⟩
    rw [shb_mem_backboneSet]
    exact shb_restrictBackbonePath_isBackbone hHG n hSupp p hp


theorem shb_backboneSelectSupport_mapLe
    {H G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (n : Current V) (hSupp : shb_CurrentSupportedOn H n)
    (x y : V) :
    Option.map (shb_pathMapLe hHG) (shb_backboneSelectSupport H n x y) =
      shb_backboneSelectSupport G n x y := by
  letI : LinearOrder (H.Path x y) := shb_supportPathOrder H x y
  letI : LinearOrder (G.Path x y) := shb_supportPathOrder G x y
  have hne := shb_backboneSet_nonempty_iff_of_supported hHG n hSupp x y
  unfold shb_backboneSelectSupport
  by_cases hH : (shb_backboneSet H n x y).Nonempty
  · have hG : (shb_backboneSet G n x y).Nonempty := hne.mp hH
    rw [dif_pos hH, dif_pos hG, Option.map_some]
    apply congrArg some
    let pH := (shb_backboneSet H n x y).min' hH
    let pG := (shb_backboneSet G n x y).min' hG
    have hpH : pH ∈ shb_backboneSet H n x y := Finset.min'_mem _ _
    have hpG : pG ∈ shb_backboneSet G n x y := Finset.min'_mem _ _
    have hmapH : shb_pathMapLe hHG pH ∈ shb_backboneSet G n x y := by
      rw [shb_mem_backboneSet] at hpH ⊢
      exact shb_mapLe_isBackboneOf hHG n pH hpH
    have hpGback : shb_IsBackboneOf G n x y pG :=
      (shb_mem_backboneSet G n x y pG).mp hpG
    let qH := shb_restrictBackbonePath hHG n hSupp pG hpGback
    have hqH : qH ∈ shb_backboneSet H n x y := by
      rw [shb_mem_backboneSet]
      exact shb_restrictBackbonePath_isBackbone hHG n hSupp pG hpGback
    have hminG : pG ≤ shb_pathMapLe hHG pH :=
      Finset.min'_le _ _ hmapH
    have hminH : pH ≤ qH := Finset.min'_le _ _ hqH
    have hmapq : shb_pathMapLe hHG qH = pG := by
      exact shb_mapLe_restrictBackbonePath hHG n hSupp pG hpGback
    have hmapMinH : shb_pathMapLe hHG pH ≤ shb_pathMapLe hHG qH := by
      change (pH.1.mapLe hHG).support ≤ (qH.1.mapLe hHG).support
      simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hminH
    exact le_antisymm (hmapMinH.trans_eq hmapq) hminG
  · have hG : ¬ (shb_backboneSet G n x y).Nonempty :=
      fun hg => hH (hne.mpr hg)
    rw [dif_neg hH, dif_neg hG, Option.map_none]


theorem shb_ofEdgeFun_supportedOn
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (m : H.edgeFinset → ℕ) :
    shb_CurrentSupportedOn H (ofEdgeFun H m) := by
  intro e he
  unfold ofEdgeFun at he
  split at he
  · rename_i hmem
    simpa [SimpleGraph.edgeFinset] using hmem
  · simp at he


theorem shb_backboneSelectSupport_ofEdgeFun_mapLe
    {H G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (m : H.edgeFinset → ℕ) (x y : V) :
    Option.map (shb_pathMapLe hHG)
        (shb_backboneSelectSupport H (ofEdgeFun H m) x y) =
      shb_backboneSelectSupport G (ofEdgeFun H m) x y :=
  shb_backboneSelectSupport_mapLe hHG (ofEdgeFun H m)
    (shb_ofEdgeFun_supportedOn H m) x y


theorem shb_backboneSelectSupport_ofEdgeFun_eq_some_mapLe_iff
    {H G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (m : H.edgeFinset → ℕ) {x y : V}
    (p : H.Path x y) :
    shb_backboneSelectSupport G (ofEdgeFun H m) x y =
        some (shb_pathMapLe hHG p) ↔
      shb_backboneSelectSupport H (ofEdgeFun H m) x y = some p := by
  have hcompat := shb_backboneSelectSupport_ofEdgeFun_mapLe hHG m x y
  rw [← hcompat]
  constructor
  · intro h
    obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp h
    have : q = p := shb_pathMapLe_injective hHG heq
    simpa [this] using hq
  · intro h
    simp [h]


end StatMech.Sharpness
